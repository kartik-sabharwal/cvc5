#include "preprocessing/passes/unroll.h"

#include "expr/node_algorithm.h"
#include "expr/node_traversal.h"
#include "expr/subs.h"
#include "options/quantifiers_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/env.h"
#include "theory/quantifiers/quantifiers_attributes.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

Unroll::Unroll(PreprocessingPassContext* ppc) : PreprocessingPass(ppc, "unroll")
{
}

PreprocessingPassResult Unroll::applyInternal(AssertionPipeline* ap)
{
  /**
   * `applyInternal` wants to unroll the definitions of only those function
   * symbols that satisfy two properties: (1) they are defined recursively and
   * (2) they occur in assertions that do not have a universal quantifier at the
   * root.  The function symbols that satisfy property (1) and the indices of
   * their definitions in the assertion pipeline go in the dictionary `defns`.
   * The function symbols that satisfy property (2) go in the set `func_syms`.
   * To reiterate -- we unroll the definitions of only those function symbols
   * that live in the intersection of `func_syms` with the set of keys of
   * `defns`.
   */

  // `defns` maps every function symbol satisfying property (1) above to the
  // index of its definition in the assertion pipeline `ap`.
  std::unordered_map<Node, size_t> defns;

  // The function symbols that satisfy property (2) above.
  std::unordered_set<Node> func_syms;

  // Populate both `defns` and `func_syms` in a single sweep over all
  // assertions.
  for (size_t i = 0; i < ap->size(); ++i)
  {
    const Node phi = (*ap)[i];
    const Node maybe_head = theory::quantifiers::QuantAttributes::getFunDefHead(phi);
    if (!maybe_head.isNull())
    {
      const Node func = maybe_head.getOperator();
      defns[func] = i;
    }

    if (phi.getKind() != Kind::FORALL)
    {
      const std::unordered_set<Node> tmp_syms = getFuncSyms(phi);
      func_syms.insert(tmp_syms.begin(), tmp_syms.end());
    }
  }

  Trace("unroll") << "defns := " << defns << std::endl;

  // `rlv` is the restriction of the map `defns` to function symbols that occur
  // in the set `func_syms`.
  std::unordered_map<Node, size_t> rlv;
  for (const Node& sym : func_syms)
  {
    rlv[sym] = defns[sym];
  }

  if (options().quantifiers.unrollFinite)
  {
    // Initialize the substitution.
    Subs tau;

    // Map each function symbol that occurs in `rlv` to a lambda.
    for (std::pair<Node, size_t> entry : rlv)
    {
      const size_t pos = std::get<1>(entry);
      const Node phi = (*ap)[pos];
      const Node psi = unroll(phi, options().quantifiers.unroll);
      const Node head = theory::quantifiers::QuantAttributes::getFunDefHead(psi);
      const Node body = theory::quantifiers::QuantAttributes::getFunDefBody(psi);
      const Node func = head.getOperator();
      std::vector<Node> formals;
      formals.insert(formals.end(), head.begin(), head.end());
      const Node lam = nodeManager()->mkNode(Kind::LAMBDA, nodeManager()->mkNode(Kind::BOUND_VAR_LIST, formals), body);
      tau.add(func, lam);
    }

    // Remove all definitions of recursive functions (i.e. replace the assertion
    // associated with each entry in `defns` with true).
    for (std::pair<Node, size_t> entry : defns)
    {
      const size_t pos = std::get<1>(entry);
      ap->replace(pos, nodeManager()->mkConst(true));
    }

    // Apply the substitution on each assertion.
    for (size_t pos = 0; pos < ap->size(); ++pos)
    {
      const Node phi = (*ap)[pos];
      Node psi = tau.apply(phi);
      if (psi != phi)
      {
        ap->replace(pos, psi);
        // Rewrite to beta-reduce lambdas.
        ap->ensureRewritten(pos);
      }
    }
  }
  else
  {
    // Each entry in the dictionary `rlv` is a mapping from a function symbol
    // `func` to an index `pos` such that the assertion at position `pos` in the
    // assertion pipeline, `phi`, is the definition of `sym`.  We replace `phi`
    // with `psi` which is the RHS of `phi` unrolled
    // `options().quantifiers.unroll` many times.

    for (const std::pair<Node, size_t> entry : rlv)
    {
      const size_t pos = std::get<1>(entry);
      const Node phi = (*ap)[pos];
      const Node psi = unroll(phi, options().quantifiers.unroll);
      ap->replace(pos, psi);
      ap->ensureRewritten(pos);
    }
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

const std::unordered_set<Node> Unroll::getFuncSyms(TNode root) const
{
  std::unordered_set<Node> result;
  std::function<bool(TNode)> skipIf = [](TNode n) {
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

Node Unroll::elimAndOr(const Node expr)
{
  enum Type
  {
    MAKE,
    BREAK
  };

  struct Job
  {
    const Type d_type;
    const Node d_expr;
    const Kind d_kind;
    const size_t d_nargs;
  };

  std::vector<Job*> jobs;
  jobs.push_back(new Job{BREAK, expr, Kind::UNDEFINED_KIND, 0});

  std::vector<Node> results;

  NodeManager* nm = nodeManager();

  while (!jobs.empty())
  {
    Job* job = jobs.back();
    jobs.pop_back();

    if (job->d_type == MAKE)
    {
      std::vector<Node> children;
      for (size_t i = 0; i < job->d_nargs; ++i)
      {
        children.push_back(results.back());
        results.pop_back();
      }

      results.push_back(nm->mkNode(job->d_kind, children));
    }
    else
    {
      const Node job_expr = job->d_expr;
      const kind::MetaKind job_expr_metakind = job_expr.getMetaKind();
      const Kind job_expr_kind = job_expr.getKind();

      if (job_expr_metakind == kind::metakind::CONSTANT
          || job_expr_metakind == kind::metakind::VARIABLE)
      {
        results.push_back(job_expr);
      }
      else if (job_expr_metakind == kind::metakind::OPERATOR)
      {
        if (job_expr_kind == Kind::AND)
        {
          const size_t nchildren = job_expr.getNumChildren();

          for (size_t i = 0; i < nchildren - 1; ++i)
          {
            jobs.push_back(new Job{MAKE, Node::null(), Kind::ITE, 3});
            jobs.push_back(
                new Job{BREAK, job_expr[i], Kind::UNDEFINED_KIND, 0});
          }

          jobs.push_back(
              new Job{BREAK, job_expr[nchildren - 1], Kind::UNDEFINED_KIND, 0});

          for (size_t i = 0; i < nchildren - 1; ++i)
          {
            jobs.push_back(
                new Job{BREAK, nm->mkConst(false), Kind::UNDEFINED_KIND, 0});
          }
        }
        else if (job_expr_kind == Kind::OR)
        {
          const size_t nchildren = job_expr.getNumChildren();

          for (size_t i = 0; i < nchildren - 1; ++i)
          {
            jobs.push_back(new Job{MAKE, Node::null(), Kind::ITE, 3});
            jobs.push_back(
                new Job{BREAK, job_expr[i], Kind::UNDEFINED_KIND, 0});
            jobs.push_back(
                new Job{BREAK, nm->mkConst(true), Kind::UNDEFINED_KIND, 0});
          }

          jobs.push_back(
              new Job{BREAK, job_expr[nchildren - 1], Kind::UNDEFINED_KIND, 0});
        }
        else
        {
          jobs.push_back(new Job{
              MAKE, Node::null(), job_expr_kind, job_expr.getNumChildren()});

          for (const Node ch : job_expr)
          {
            jobs.push_back(new Job{BREAK, ch, Kind::UNDEFINED_KIND, 0});
          }
        }
      }
      else if (job_expr_metakind == kind::metakind::PARAMETERIZED)
      {
        jobs.push_back(new Job{
            MAKE, Node::null(), job_expr_kind, job_expr.getNumChildren() + 1});
        jobs.push_back(
            new Job{BREAK, job_expr.getOperator(), Kind::UNDEFINED_KIND, 0});

        for (const Node ch : job_expr)
        {
          jobs.push_back(new Job{BREAK, ch, Kind::UNDEFINED_KIND, 0});
        }
      }
      else
      {
        results.push_back(job_expr);
      }
    }

    delete job;
  }

  return results.back();
}

Node Unroll::unroll(const Node phi, size_t fuel)
{
  // We fetch the name of the function symbol, `func`, whose definition we want
  // to unroll.
  const Node head = theory::quantifiers::QuantAttributes::getFunDefHead(phi);
  const Node func = head.getOperator();

  // Get the body of the definition of the function symbol `func`.
  const Node body = theory::quantifiers::QuantAttributes::getFunDefBody(phi);

  // For now we call elimAndOr here.
  const Node body_ite = elimAndOr(body);
  const Node base_case = baseCase(func, body_ite);

  // We maintain a node to hold the current unrolling of the body of `func`.
  // For each iteration of the loop below we collect the set of calls to `func`
  // in `unrolled_body`.  From this set we remove the calls to `func` that are
  // proper subterms of other calls to `func`.  Let's call this the set of
  // top-level calls.  We iterate through the list of top-level calls and spend
  // a unit of fuel to unroll each call exactly once.  In case we run out of
  // fuel we unroll the call to itself.
  Node unrolled_body = body;
  while (fuel > 0)
  {
    // We collect all calls to uninterpreted functions in `unrolled_body` in
    // `uf_calls`.
    std::unordered_set<Node> uf_calls;
    expr::getSubtermsKind(Kind::APPLY_UF, unrolled_body, uf_calls);

    // We collect all calls to `func` in `unrolled_body` in `func_calls`.
    std::unordered_set<Node> func_calls;
    for (const Node& call : uf_calls)
    {
      if (call.getOperator() == func)
      {
        func_calls.insert(call);
      }
    }

    // These are calls to uninterpreted functions that are proper subterms of
    // the calls to `func` in `unrolled_body`.
    std::unordered_set<Node> nested_calls;
    for (const Node& call : func_calls)
    {
      expr::getSubtermsKind(Kind::APPLY_UF, call, nested_calls);
      nested_calls.erase(call);
    }

    // These are the top-level calls to `func` in `unrolled_body`.  In other
    // words these are the calls to `func` in `unrolled_body` that do not occur
    // within other calls to `func`.
    std::vector<Node> top_level_calls;
    for (const Node& call : func_calls)
    {
      if (nested_calls.find(call) == nested_calls.end())
      {
        top_level_calls.push_back(call);
      }
    }

    // We construct a substitution `tau` that maps each `call` in
    // `top_level_calls` to its one-step unrolling if there was fuel to spend in
    // the loop, or itself if there was no fuel to spend in the loop.  For each
    // `call` if there is fuel to spend we construct a substitution `sigma` that
    // maps the formal parameters -- the children of `head` -- to the actual
    // parameters -- the children of `call`.  In `tau` we map `call` to the
    // result of applying the substitution `sigma` to `body`.
    Subs tau;
    for (const Node& call : top_level_calls)
    {
      if (fuel > 0)
      {
        Subs sigma;
        for (size_t ch = 0; ch < call.getNumChildren(); ++ch)
        {
          sigma.add(head[ch], call[ch]);
        }

        tau.add(call, sigma.apply(body));

        --fuel;
      }
      else
      {
        break;
      }
    }

    // We update `unrolled_body` by applying `tau` to it.
    unrolled_body = tau.apply(unrolled_body);
  }

  if (options().quantifiers.unrollFinite)
  {
    // We want to remove all calls to `func` in `unrolled_body`.  We first
    // collect all calls to uninterpreted functions in `unrolled_body` in
    // `uf_calls`.  We filter `uf_calls` to keep only calls of `func` naming the
    // result `func_calls`.  We make `func_calls` a vector because we will care
    // about the order of its elements.  Some elements of `func_calls` may be
    // proper subexpressions of other elements of `func_calls`.  To handle this
    // we sort `func_calls` so that proper subterms occur before their parents.
    // We also initialize a substitution `tau`.  We run the loop while
    // `func_calls` is non-empty.  We take the first element of `func_calls`.
    // We map it to its base case unrolling in the substitution `tau`.  We dump
    // the contents of `func_calls` in a temporary vector `tmp`, emptying the
    // former.  We then dump the contents of `tmp` back into `func_calls` but
    // after taking their images under `tau`.

    std::unordered_set<Node> uf_calls;
    expr::getSubtermsKind(Kind::APPLY_UF, unrolled_body, uf_calls);

    std::vector<Node> func_calls;
    func_calls.insert(func_calls.end(), uf_calls.begin(), uf_calls.end());

    std::sort(func_calls.begin(), func_calls.end());

    Subs tau;

    while (!func_calls.empty())
    {
      Node call0 = func_calls[0];

      Subs sigma;
      for (size_t ch = 0; ch < call0.getNumChildren(); ++ch)
      {
        sigma.add(head[ch], call0[ch]);
      }

      Node expansion0 = sigma.apply(base_case);

      tau.add(call0, expansion0);

      const size_t n = func_calls.size() - 1;
      std::vector<Node> tmp;
      for (size_t i = 0; i < n; ++i)
      {
        tmp.push_back(func_calls.back());
        func_calls.pop_back();
      }
      func_calls.pop_back();

      for (size_t i = 0; i < n; ++i)
      {
        func_calls.push_back(tau.apply(tmp.back()));
        tmp.pop_back();
      }
    }

    unrolled_body = tau.apply(unrolled_body);
  }

  NodeManager* nm = nodeManager();
  const Node psi = nm->mkNode(Kind::FORALL,
                              phi[0],
                              nm->mkNode(Kind::EQUAL, head, unrolled_body),
                              phi[2]);

  return psi;
}

Node Unroll::baseCase(const Node func, const Node expr)
{
  enum JobType
  {
    BREAK,
    MAKE
  };

  enum ResultType
  {
    NODE,
    FAIL
  };

  struct Job
  {
    const JobType d_type;
    const Node d_expr;
  };

  struct Result
  {
    const ResultType d_type;
    const Node d_expr;
  };

  std::vector<Job*> jobs;
  jobs.push_back(new Job{BREAK, expr});

  std::vector<Result> results;

  NodeManager* nm = nodeManager();

  while (!jobs.empty())
  {
    Job* job = jobs.back();
    jobs.pop_back();

    if (job->d_type == MAKE)
    {
      Result test_result = results.back();
      Node test = test_result.d_expr;
      results.pop_back();

      Result conseq_result = results.back();
      Node conseq = conseq_result.d_expr;
      results.pop_back();

      Result alt_result = results.back();
      Node alt = alt_result.d_expr;
      results.pop_back();

      if (test_result.d_type == FAIL)
      {
        results.push_back(Result{FAIL, Node::null()});
      }
      else if (conseq_result.d_type == FAIL && alt_result.d_type == NODE)
      {
        results.push_back(Result{NODE, alt});
      }
      else if (alt_result.d_type == FAIL && conseq_result.d_type == NODE)
      {
        results.push_back(Result{NODE, conseq});
      }
      else if (alt_result.d_type == NODE && conseq_result.d_type == NODE)
      {
        results.push_back(
            Result{NODE, nm->mkNode(Kind::ITE, test, conseq, alt)});
      }
      else
      {
        results.push_back(Result{FAIL, Node::null()});
      }
    }
    else
    {
      Node job_expr = job->d_expr;
      Kind job_expr_kind = job_expr.getKind();

      if (job_expr_kind == Kind::ITE)
      {
        jobs.push_back(new Job{MAKE, Node::null()});
        jobs.push_back(new Job{BREAK, job_expr[0]});
        jobs.push_back(new Job{BREAK, job_expr[1]});
        jobs.push_back(new Job{BREAK, job_expr[2]});
      }
      else
      {
        std::unordered_set<Node> uf_calls;
        expr::getSubtermsKind(Kind::APPLY_UF, job_expr, uf_calls);

        bool has_func_call = false;
        for (const Node& call : uf_calls)
        {
          if (call.getOperator() == func)
          {
            has_func_call = true;
          }
        }

        if (has_func_call)
        {
          results.push_back(Result{FAIL, Node::null()});
        }
        else
        {
          results.push_back(Result{NODE, job_expr});
        }
      }
    }

    delete job;
  }

  Result result = results.back();

  Node result_node;
  if (result.d_type == NODE)
  {
    result_node = result.d_expr;
  }

  return result_node;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
