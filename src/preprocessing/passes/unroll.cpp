#include "preprocessing/passes/unroll.h"

#include "expr/subs.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/env.h"
#include "preprocessing/assertion_pipeline.h"
#include "expr/node_traversal.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "options/quantifiers_options.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

Unroll::Unroll(PreprocessingPassContext* ppc)
    : PreprocessingPass(ppc, "unroll") 
{
  d_first_time = true;
}

PreprocessingPassResult Unroll::applyInternal(AssertionPipeline* ap)
{
  // Function symbols that do not occur within the scope of a universal or
  // existential quantifier.
  std::unordered_set<Node> func_syms;

  // Function symbols that are associated with a recursive definition mapped to
  // the assertion index of their definition.
  std::unordered_map<Node, size_t> defns;

  // Populate both containers in a single sweep over all assertions.
  for (size_t i = 0; i < ap->size(); ++i)
  {
    const Node& phi = (*ap)[i];
    if (phi.getKind() == Kind::FORALL)
    {
      TNode body = phi[1];
      if (body.getKind() == Kind::EQUAL)
      {
        TNode lhs = body[0];
        if (lhs.hasAttribute(theory::FunDefAttribute()))
        {
          defns[lhs.getOperator()] = i;
        }
      }
    }
    else
    {
      const std::unordered_set<Node> tmp_syms = getFuncSyms(phi);
      func_syms.insert(tmp_syms.begin(), tmp_syms.end());
    }
  }

  // The map at the intersection of the domain of defns with the set func_syms.
  std::unordered_map<Node, size_t> rlv;
  for (const Node& sym : func_syms)
  {
    rlv[sym] = defns[sym];
  }

  Trace("unroll") << "(defined";
  for (const std::pair<Node, size_t> entry : defns)
  {
    Trace("unroll") << " " << std::get<0>(entry);
  }
  Trace("unroll") << ")" << std::endl;

  Trace("unroll") << "(mentioned";
  for (const Node& sym : func_syms)
  {
    Trace("unroll") << " " << sym;
  }
  Trace("unroll") << ")" << std::endl;

  Trace("unroll") << "(relevant";
  for (const std::pair<Node, size_t> entry : rlv)
  {
    Trace("unroll") << " " << std::get<0>(entry);
  }
  Trace("unroll") << ")" << std::endl;

  // Now for each assertion index in rlv replace the assertion at that index
  // with an n-fold unrolling.
  NodeManager* nm = nodeManager();
  for (const std::pair<Node, size_t> entry : rlv)
  {
    const size_t pos = std::get<1>(entry);
    const Node phi = (*ap)[pos];
    const Node app = theory::quantifiers::QuantAttributes::getFunDefHead(phi);
    Trace("SolverEngine::unroll") << "(" << std::endl
                                  << "(phi " << phi << ")" << std::endl
                                  << "(app " << app << ")" << std::endl
                                  << ")" << std::endl;
    Trace("unroll") << "phi has " << phi.getNumChildren() << " children" << std::endl;
    const Node func = std::get<0>(entry);
    std::vector<Node> formals;
    formals.insert(formals.end(), app.begin(), app.end());
    const Node body = theory::quantifiers::QuantAttributes::getFunDefBody(phi);
    const Node new_body = unroll(func, formals, body, options().quantifiers.unroll);
    const Node psi = nm->mkNode(Kind::FORALL, phi[0], nm->mkNode(Kind::EQUAL, app, new_body), phi[2]);
    Trace("unroll") << "psi has " << psi.getNumChildren() << " children" << std::endl;
    Trace("unroll") << "(psi " << psi << ")" << std::endl;
    ap->replace(pos, psi);
    Trace("unroll") << "(before-rewriting " << (*ap)[pos][1][0].getAttribute(theory::FunDefAttribute()) << ")" << std::endl;
    ap->ensureRewritten(pos);
    Trace("unroll") << "(after-rewriting " << (*ap)[pos][1][0].getAttribute(theory::FunDefAttribute()) << ")" << std::endl;
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

const std::unordered_set<Node> Unroll::getFuncSyms(TNode root) const
{
  std::unordered_set<Node> result;
  std::function<bool(TNode)> skipIf = [](TNode n)
    {
      const Kind k = n.getKind();
      return (k == Kind::FORALL || k == Kind::EXISTS);
    };
  NodeDfsIterable root_iterable(root, VisitOrder::POSTORDER, skipIf);
  NodeDfsIterator root_it = root_iterable.begin();
  NodeDfsIterator root_end = root_iterable.end();
  for (; root_it != root_end; ++root_it)
  {
    TNode curr = *root_it;
    if (curr.getKind() == Kind::APPLY_UF)
    {
      result.insert(curr.getOperator());
    }
  }
  return result;
}

Unroll::AbstractionData Unroll::makeAbstraction(
    const Node func, const std::vector<Node> formals, const Node formula)
{
  const TypeNode func_typ = func.getType().getRangeType();

  size_t n_calls = 0;
  std::vector<Node> calls;
  std::vector<Node> abs_vars;

  enum JobKind
  {
    MAKE,
    BREAK
  };

  struct Job
  {
    const JobKind d_job_kind;
    const Node d_expr;
    const kind::MetaKind d_metakind;
    const Kind d_kind;
    const size_t d_num_pop;
  };

  std::vector<Job*> jobs;
  std::vector<Node> results;

  jobs.push_back(new Job{
      BREAK, formula, kind::metakind::INVALID, Kind::UNDEFINED_KIND, 0});

  NodeManager* node_mgr = d_env.getNodeManager();

  while (!jobs.empty())
  {
    Job* job = jobs.back();
    jobs.pop_back();

    switch (job->d_job_kind)
    {
      case BREAK:
      {
        const Node expr = job->d_expr;

        switch (expr.getMetaKind())
        {
          case kind::metakind::PARAMETERIZED:
          {
            const Kind expr_kind = expr.getKind();
            const Node expr_op = expr.getOperator();

            if (expr_kind == Kind::APPLY_UF && expr_op == func)
            {
              std::ostringstream name;
              name << "h" << n_calls;

              Node abs_var = node_mgr->mkBoundVar(name.str(), func_typ);

              calls.push_back(expr);

              abs_vars.push_back(abs_var);

              results.push_back(abs_var);

              ++n_calls;
            }
            else
            {
              const size_t n_children = expr.getNumChildren();

              jobs.push_back(new Job{MAKE,
                                     Node::null(),
                                     kind::metakind::PARAMETERIZED,
                                     expr_kind,
                                     n_children + 1});

              jobs.push_back(new Job{BREAK,
                                     expr_op,
                                     kind::metakind::INVALID,
                                     Kind::UNDEFINED_KIND,
                                     0});

              for (size_t i = 0; i < n_children; ++i)
              {
                jobs.push_back(new Job{BREAK,
                                       expr[i],
                                       kind::metakind::INVALID,
                                       Kind::UNDEFINED_KIND,
                                       0});
              }
            }

            break;
          }

          case kind::metakind::OPERATOR:
          {
            const size_t n_children = expr.getNumChildren();

            jobs.push_back(new Job{MAKE,
                                   Node::null(),
                                   kind::metakind::OPERATOR,
                                   expr.getKind(),
                                   n_children});

            for (size_t i = 0; i < n_children; ++i)
            {
              jobs.push_back(new Job{BREAK,
                                     expr[i],
                                     kind::metakind::INVALID,
                                     Kind::UNDEFINED_KIND,
                                     0});
            }

            break;
          }

          case kind::metakind::CONSTANT:
          case kind::metakind::VARIABLE:
          {
            results.push_back(expr);

            break;
          }

          default:
          {
            Assert(false);
            break;
          }
        }

        break;
      }

      case MAKE:
      {
        const Kind expr_kind = job->d_kind;

        std::vector<Node> args;

        for (size_t i = 0; i < job->d_num_pop; i++)
        {
          args.push_back(results.back());
          results.pop_back();
        }

        // Trace("SolverEngine::makeAbstraction") << "(" << expr_kind;
        // for (size_t i = 0; i < job->d_num_pop; i++)
        // {
        //   Trace("SolverEngine::makeAbstraction") << " " << args[i];
        // }
        // Trace("SolverEngine::makeAbstraction") << ")" << std::endl;

        const Node result = node_mgr->mkNode(expr_kind, args);

        results.push_back(result);

        break;
      }

      default:
      {
        Assert(false);
        break;
      }
    }

    delete job;
  }

  const Node result = results.back();
  results.pop_back();

  if (TraceIsOn("SolverEngine::makeAbstraction"))
  {
    std::ostringstream msg;

    msg << "(";
    msg << "(abstraction " << result << ")";
    msg << " (calls";
    for (size_t i = 0; i < n_calls; ++i)
    {
      msg << " (";
      msg << i << " . " << calls[i];
      msg << ")";
    }
    msg << ")";
    msg << " (variables";
    for (size_t i = 0; i < n_calls; ++i)
    {
      msg << " (";
      msg << i << " . " << abs_vars[i];
      msg << ")";
    }
    msg << ")";
    msg << ")" << std::endl;

    Trace("SolverEngine::makeAbstraction") << msg.str();
  }

  return Unroll::AbstractionData{result, abs_vars, n_calls, calls};
}

Node Unroll::uniquify(const Node body)
{
  enum JobKind
  {
    BREAK,
    MAKE,
    FRESHEN
  };

  struct Job
  {
    const JobKind d_job_kind;  // ALL
    const Node d_node;         // BREAK, FRESHEN
    const Kind d_kind;         // MAKE
    const size_t d_num_args;   // MAKE
    const Node d_pat;          // FRESHEN

    static Job mkBreak(const Node node)
    {
      return Job{BREAK, node, Kind::UNDEFINED_KIND, 0, Node::null()};
    }

    static Job mkMake(const Kind kind, const size_t num_args)
    {
      return Job{MAKE, Node::null(), kind, num_args, Node::null()};
    }

    static Job mkFreshen(const Node bvs, const Node pat)
    {
      return Job{FRESHEN, bvs, Kind::UNDEFINED_KIND, 0, pat};
    }

    std::string toString()
    {
      // msg is short for message.
      std::ostringstream msg;

      switch (d_job_kind)
      {
        case BREAK:
        {
          msg << "(Break " << d_node << ")";
          break;
        }
        case MAKE:
        {
          msg << "(Make " << d_kind << " " << d_num_args << ")";
          break;
        }
        case FRESHEN:
        {
          msg << "(Freshen " << d_node << " " << d_pat << ")";
          break;
        }
      }

      return msg.str();
    }
  };

  std::vector<Job> jobs = {Job::mkBreak(body)};
  std::vector<Node> results;
  NodeManager* node_mgr = d_env.getNodeManager();

  while (!jobs.empty())
  {
    Job job = jobs.back();
    jobs.pop_back();

    const JobKind jk = job.d_job_kind;

    switch (jk)
    {
      case BREAK:
      {
        const Node node = job.d_node;

        // nmk is 'metakind of node'.
        const kind::MetaKind nmk = node.getMetaKind();

        // nk is 'kind of node'
        const Kind nk = node.getKind();

        switch (nmk)
        {
          case kind::metakind::CONSTANT:
          case kind::metakind::VARIABLE:
          {
            results.push_back(node);
            break;
          }

          case kind::metakind::PARAMETERIZED:
          {
            jobs.push_back(Job::mkMake(nk, node.getNumChildren() + 1));

            jobs.push_back(Job::mkBreak(node.getOperator()));

            for (Node::iterator ch = node.begin(); ch != node.end(); ++ch)
            {
              jobs.push_back(Job::mkBreak(*ch));
            }

            break;
          }

          case kind::metakind::OPERATOR:
          {
            switch (nk)
            {
              case Kind::MATCH_BIND_CASE:
              {
                jobs.push_back(Job::mkFreshen(node[0], node[1]));

                jobs.push_back(Job::mkBreak(node[2]));

                break;
              }

              default:
              {
                jobs.push_back(Job::mkMake(nk, node.getNumChildren()));

                for (Node::iterator ch = node.begin(); ch != node.end(); ++ch)
                {
                  jobs.push_back(Job::mkBreak(*ch));
                }

                break;
              }
            }
            break;
          }

default:
{
  break;
}

        }
      break;
      }

      case MAKE:
      {
        const Kind kind = job.d_kind;
        const size_t num_args = job.d_num_args;

        std::vector<Node> args;
        for (size_t i = 0; i < num_args; i++)
        {
          args.push_back(results.back());
          results.pop_back();
        }

        const Node node = node_mgr->mkNode(kind, args);

        results.push_back(node);

        break;
      }

      case FRESHEN:
      {
        // Grab the bound variables.
        const Node bvs = job.d_node;

        // Grab the pattern.
        const Node pat = job.d_pat;

        // Grab the body.
        const Node case_body = results.back();
        results.pop_back();

        // Construct the substitution.
        Subs sigma;
        for (Node::iterator bv_ref = bvs.begin(); bv_ref != bvs.end(); ++bv_ref)
        {
          const Node bv = *bv_ref;

          sigma.add(bv, node_mgr->mkBoundVar(bv.getType()));
        }

        // Apply the substitution to the bound variable list.
        const Node new_bvs = sigma.apply(bvs);

        // Apply the substitution to the pattern.
        const Node new_pat = sigma.apply(pat);

        // Apply the substitution to the body.
        const Node new_case_body = sigma.apply(case_body);

        // Construct a Node with kind MATCH_BIND_CASE.
        const Node node = node_mgr->mkNode(
            Kind::MATCH_BIND_CASE,
            std::vector<Node>{new_bvs, new_pat, new_case_body});

        // Push it on to the result stack.
        results.push_back(node);

        break;
      }
    }
  }

  const Node result = results.back();
  results.clear();

  Trace("SolverEngine::uniquify")
      << "(uniquify " << body << " " << result << ")" << std::endl;

  return result;
}

void Unroll::deconstruct(const Node body)
{
  // At this moment our only purpose is to better understand 'body'.
  // We're going to traverse it in a depth-first left-to-right fashion and print
  // all the nodes as we go along.

  typedef Node Job;

  std::vector<Job> jobs = {body};

  while (!jobs.empty())
  {
    Job job = jobs.back();
    jobs.pop_back();

    switch (job.getMetaKind())
    {
      case kind::metakind::OPERATOR:
      {
        Trace("SolverEngine::uniquify") << job.getKind() << std::endl;

        for (Node::const_reverse_iterator ch = job.rbegin(); ch != job.rend();
             ++ch)
        {
          jobs.push_back(*ch);
        }

        break;
      }
      case kind::metakind::PARAMETERIZED:
      {
        Trace("SolverEngine::uniquify") << job.getKind() << std::endl;

        for (Node::const_reverse_iterator ch = job.rbegin(); ch != job.rend();
             ++ch)
        {
          jobs.push_back(*ch);
        }

        jobs.push_back(job.getOperator());

        break;
      }
      case kind::metakind::CONSTANT:
      case kind::metakind::VARIABLE:
      {
        Trace("SolverEngine::uniquify") << job << std::endl;

        break;
      }
      default:
      {
        Assert(false);
      }
    }
  }
}

Node Unroll::unroll(const Node func,
                          const std::vector<Node> formals,
                          const Node formula,
                          const size_t count)
{
  AbstractionData abs_dat = makeAbstraction(func, formals, formula);

  const Node body = std::get<0>(abs_dat);
  const std::vector<Node> vars = std::get<1>(abs_dat);
  const size_t n_calls = std::get<2>(abs_dat);
  const std::vector<Node> calls = std::get<3>(abs_dat);

  Assert(vars.size() == calls.size() && calls.size() == n_calls);

  std::vector<Subs> xforms;
  for (const Node& a_call : calls)
  {
    Subs xform;

    Trace("SolverEngine::unroll") << "a_call == " << a_call << " and formals == " << formals << std::endl;
    Assert(a_call.getNumChildren() == formals.size());

    for (size_t i = 0; i < a_call.getNumChildren(); ++i)
    {
      xform.add(formals[i], a_call[i]);
    }

    xforms.push_back(xform);
  }

  enum JobKind
  {
    UNROLL,
    COMBINE
  };

  struct Job
  {
    const JobKind d_job_kind;
    const size_t d_count;
    Subs d_xform;
  };

  std::vector<Job*> jobs;
  std::vector<Node> results;

  Subs id;
  for (const Node& x : formals)
  {
    id.add(x, x);
  }

  jobs.push_back(new Job{UNROLL, count, id});

  NodeManager* node_mgr = d_env.getNodeManager();

  while (!jobs.empty())
  {
    if (TraceIsOn("SolverEngine::unroll"))
    {
      std::ostringstream msg;

      msg << "(jobs";
      for (const Job* job : jobs)
      {
        msg << " (job " << (job->d_job_kind == UNROLL ? "UNROLL" : "COMBINE")
            << " " << job->d_count << " " << (job->d_xform).toString() << ")";
      }
      msg << ")" << std::endl;

      msg << "(results";
      for (const Node& res : results)
      {
        msg << " " << res;
      }
      msg << ")" << std::endl;

      Trace("SolverEngine::unroll") << msg.str();
    }

    Job* job = jobs.back();
    jobs.pop_back();

    switch (job->d_job_kind)
    {
      case UNROLL:
      {
        // cnt --> count, so as not to shadow the argument of the same name.
        const size_t cnt = job->d_count;
        const Subs& job_xform = job->d_xform;

        if (cnt == 0)
        {
          std::vector<Node> args;
          args.push_back(func);
          for (const Node& x : formals)
          {
            args.push_back(job_xform.apply(x));
          }

          const Node result = node_mgr->mkNode(Kind::APPLY_UF, args);

          results.push_back(result);
        }
        else
        {
          jobs.push_back(new Job{COMBINE, 0, job_xform});

          for (size_t i = 0; i < n_calls; ++i)
          {
            Subs next_xform;
            next_xform.append(xforms[i]);
            job_xform.applyToRange(next_xform);

            jobs.push_back(new Job{UNROLL, cnt - 1, next_xform});
          }
        }

        break;
      }

      case COMBINE:
      {
        Subs& job_xform = job->d_xform;

        Subs concretes;
        for (size_t i = 0; i < n_calls; ++i)
        {
          const Node concrete = results.back();
          results.pop_back();

          concretes.add(vars[i], concrete);
        }
        concretes.append(job_xform);

        const Node result = concretes.apply(body);

        Trace("SolverEngine::unroll") << "(combine " << concretes << " " << body
                                      << " " << result << ")" << std::endl;

        results.push_back(result);

        break;
      }

      default:
      {
        Assert(false);
        break;
      }
    }

    delete job;
  }

  const Node result = results.back();
  results.clear();

  Trace("SolverEngine::unroll") << "(unroll " << result << ")" << std::endl;

  return result;
}

} // namespace passes
} // namespace preprocessing
} // namespace cvc5::internal

