/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of techniques for evaluating terms with recursively
 * defined functions.
 */

#include "theory/quantifiers/fun_def_evaluator.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/rewriter.h"
#include "theory/uf/equality_engine.h"
#include "expr/node_traversal.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

FunDefEvaluator::FunDefEvaluator(Env& env, QuantifiersState& qs)
    : EnvObj(env), d_qstate(qs)
{
}

bool FunDefEvaluator::assertDefinition(Node q)
{
  Trace("fd-eval") << "FunDefEvaluator: assertDefinition " << q << std::endl;
  Node head = QuantAttributes::getFunDefHead(q);
  if (head.isNull())
  {
    size_t index;
    if (getDefinitionIndex(q, index))
    {
      Assert(q[1].getKind() == Kind::EQUAL);
      addDefinition(q[1][index], q[1][1 - index], q);
      return true;
    }
    Trace("fd-eval") << "...not a definition" << std::endl;
    // not a function definition
    return false;
  }
  Node body = QuantAttributes::getFunDefBody(q);
  Assert(!body.isNull());
  addDefinition(head, body, q);
  return true;
}

bool FunDefEvaluator::isDefinition(const Node& q) const
{
  size_t index;
  return getDefinitionIndex(q, index);
}

bool FunDefEvaluator::getDefinitionIndex(const Node& q, size_t& index) const
{
  Assert(q.getKind() == Kind::FORALL);
  if (q[1].getKind() == Kind::EQUAL)
  {
    size_t nvars = q[0].getNumChildren();
    // check if we are (f x) = t or t = (f x).
    for (size_t i = 0; i < 2; i++)
    {
      size_t nchild = q[1][i].getNumChildren();
      if (q[1][i].getKind() != Kind::APPLY_UF || nchild != nvars)
      {
        continue;
      }
      bool isMacro = true;
      // if this side of the equality is (f x1 ... xn) where the quantified
      // formula is (forall ((x1 T1) ... (xn Tn)) ...).
      for (size_t j = 0; j < nvars; j++)
      {
        if (q[1][i][j] != q[0][j])
        {
          isMacro = false;
          break;
        }
      }
      if (isMacro)
      {
        index = i;
        return true;
      }
    }
  }
  return false;
}

void FunDefEvaluator::addDefinition(const Node& head,
                                    const Node& body,
                                    const Node& q)
{
  // h possibly with zero arguments?
  Node f = head.hasOperator() ? head.getOperator() : head;
  Assert(d_funDefMap.find(f) == d_funDefMap.end())
      << "FunDefEvaluator::assertDefinition: function already defined";
  d_funDefs.push_back(q);
  FunDefInfo& fdi = d_funDefMap[f];
  fdi.d_quant = q;
  fdi.d_body = body;
  fdi.d_args.insert(fdi.d_args.end(), q[0].begin(), q[0].end());
  Trace("fd-eval") << "FunDefEvaluator: function " << f << " is defined with "
                   << fdi.d_args << " / " << fdi.d_body << std::endl;
}

Node FunDefEvaluator::evaluateDefinitions(Node n) const
{
  // should do standard rewrite before this call
  Assert(rewrite(n) == n);
  Trace("fd-eval") << "FunDefEvaluator: evaluateDefinitions " << n << std::endl;
  NodeManager* nm = nodeManager();
  std::unordered_map<TNode, unsigned> funDefCount;
  std::unordered_map<TNode, unsigned>::iterator itCount;
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  // to ensure all nodes are ref counted
  std::unordered_set<Node> keep;
  std::map<Node, FunDefInfo>::const_iterator itf;
  std::vector<TNode> visit;
  TNode cur;
  TNode curEval;
  Node f;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    Trace("fd-eval-debug") << "evaluate subterm " << cur << std::endl;

    if (it == visited.end())
    {
      if (cur.isConst())
      {
        Trace("fd-eval-debug") << "constant " << cur << std::endl;
        visited[cur] = cur;
      }
      else if (cur.getKind() == Kind::ITE)
      {
        Trace("fd-eval-debug") << "ITE " << cur << std::endl;
        visited[cur] = Node::null();
        visit.push_back(cur);
        visit.push_back(cur[0]);
      }
      else
      {
        Trace("fd-eval-debug") << "recurse " << cur << std::endl;
        visited[cur] = Node::null();
        visit.push_back(cur);
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    }
    else
    {
      curEval = it->second;
      if (curEval.isNull())
      {
        Trace("fd-eval-debug") << "from arguments " << cur << std::endl;
        Node ret = cur;
        bool childChanged = false;
        std::vector<Node> children;
        Kind ck = cur.getKind();
        // If a parameterized node that is not APPLY_UF (which is handled below,
        // we add it to the children vector.
        if (ck != Kind::APPLY_UF
            && cur.getMetaKind() == metakind::PARAMETERIZED)
        {
          children.push_back(cur.getOperator());
        }
        else if (ck == Kind::ITE)
        {
          // get evaluation of condition
          it = visited.find(cur[0]);
          Assert(it != visited.end());
          Assert(!it->second.isNull());
          if (!it->second.isConst())
          {
            Trace("fd-eval") << "FunDefEvaluator: couldn't reduce condition of "
                                "ITE to const, FAIL\n";

            Trace("fd-eval")
                << "...failing eval was " << it->second << std::endl;
            return Node::null();
          }
          // pick child to evaluate depending on condition eval
          unsigned childIdxToEval = it->second.getConst<bool>() ? 1 : 2;
          Trace("fd-eval-debug2")
              << "FunDefEvaluator: result of ITE condition : "
              << it->second.getConst<bool>() << "\n";
          // the result will be the result of evaluation the child
          visited[cur] = cur[childIdxToEval];
          // push back self and child. The child will be evaluated first and
          // result will be the result of evaluation child
          visit.push_back(cur);
          visit.push_back(cur[childIdxToEval]);
          Trace("fd-eval-debug2") << "FunDefEvaluator: result will be from : "
                                  << cur[childIdxToEval] << "\n";
          continue;
        }
        unsigned child CVC5_UNUSED = 0;
        for (const Node& cn : cur)
        {
          it = visited.find(cn);
          Assert(it != visited.end());
          Assert(!it->second.isNull());
          childChanged = childChanged || cn != it->second;
          children.push_back(it->second);
          Trace("fd-eval-debug2") << "argument " << child++
                                  << " eval : " << it->second << std::endl;
        }
        if (cur.getKind() == Kind::APPLY_UF)
        {
          // need to evaluate it
          f = cur.getOperator();
          Trace("fd-eval-debug2")
              << "FunDefEvaluator: need to eval " << f << "\n";
          itf = d_funDefMap.find(f);
          itCount = funDefCount.find(f);
          if (itCount == funDefCount.end())
          {
            funDefCount[f] = 0;
            itCount = funDefCount.find(f);
          }
          if (itf == d_funDefMap.end()
              || itCount->second > options().quantifiers.sygusRecFunEvalLimit)
          {
            Trace("fd-eval")
                << "FunDefEvaluator: "
                << (itf == d_funDefMap.end() ? "no definition for "
                                             : "too many evals for ")
                << f << ", FAIL" << std::endl;
            return Node::null();
          }
          ++funDefCount[f];
          // get the function definition
          Node sbody = itf->second.d_body;
          Trace("fd-eval-debug2")
              << "FunDefEvaluator: definition: " << sbody << "\n";
          const std::vector<Node>& args = itf->second.d_args;
          if (!args.empty())
          {
            // invoke it on arguments using the evaluator
            sbody = evaluate(sbody, args, children);
            if (TraceIsOn("fd-eval-debug2"))
            {
              Trace("fd-eval-debug2")
                  << "FunDefEvaluator: evaluation with args:\n";
              for (const Node& ch : children)
              {
                Trace("fd-eval-debug2") << "..." << ch << "\n";
              }
              Trace("fd-eval-debug2")
                  << "FunDefEvaluator: results in " << sbody << "\n";
            }
            Assert(!sbody.isNull());
          }
          keep.insert(sbody);
          // our result is the result of the body
          visited[cur] = sbody;
          // If its not constant, we push back self and the substituted body.
          // Thus, we evaluate the body first; our result will be the result of
          // evaluating the body.
          if (!sbody.isConst())
          {
            Trace("fd-eval-debug2") << "FunDefEvaluator: will map " << cur
                                    << " from body " << sbody << "\n";
            visit.push_back(cur);
            visit.push_back(sbody);
          }
        }
        else
        {
          if (childChanged)
          {
            ret = nm->mkNode(cur.getKind(), children);
            ret = rewrite(ret);
            keep.insert(ret);
          }
          Trace("fd-eval-debug2") << "built from arguments " << ret << "\n";
          visited[cur] = ret;
        }
      }
      else if (cur != curEval && !curEval.isConst())
      {
        Trace("fd-eval-debug") << "from body " << cur << std::endl;
        Trace("fd-eval-debug") << "and eval  " << curEval << std::endl;
        // we had to evaluate our body, which should have a definition now
        it = visited.find(curEval);
        if (it == visited.end())
        {
          Trace("fd-eval-debug2") << "eval without definition\n";
          // this is the case where curEval was not a constant but it was
          // irreducible, for example (DT_SYGUS_EVAL e args)
          visited[cur] = curEval;
        }
        else
        {
          Trace("fd-eval-debug2")
              << "eval with definition " << it->second << "\n";
          visited[cur] = it->second;
        }
      }
    }
  } while (!visit.empty());
  Trace("fd-eval") << "FunDefEvaluator: return " << visited[n] << ", SUCCESS\n";
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

Node FunDefEvaluator::evaluateDefinitionsSymbolically(Node n, size_t fuel) const
{
  enum JobKind {EVAL, BAN, UNBAN, CHECK, BRANCH, COMBINE};

  struct Job
  {
    JobKind d_job_kind;
    Node d_nodes[2];
    Kind d_node_kind;
    size_t d_num_args;

    static Job makeEval(Node n)
    {
      return Job{EVAL, {n, Node::null()}, Kind::UNDEFINED_KIND, 0};
    }

    static Job makeBan(Node n)
    {
      return Job{BAN, {n, Node::null()}, Kind::UNDEFINED_KIND, 0};
    }

    static Job makeUnban(Node n)
    {
      return Job{UNBAN, {n, Node::null()}, Kind::UNDEFINED_KIND, 0};
    }

    static Job makeCheck(Node n0, Node n1)
    {
      return Job{CHECK, {n0, n1}, Kind::UNDEFINED_KIND, 0};
    }

    static Job makeBranch(Node n0, Node n1)
    {
      return Job{BRANCH, {n0, n1}, Kind::UNDEFINED_KIND, 0};
    }

    static Job makeCombine(Kind k, size_t num_args)
    {
      return Job{COMBINE, {Node::null(), Node::null()}, k, num_args};
    }

    std::string toString() const
    {
      std::ostringstream pretty;
      switch (d_job_kind)
      {
        case EVAL: 
        {
          pretty << "(EVAL " << d_nodes[0] << ")";
          break;
        }
        case BAN: 
        {
          pretty << "(BAN " << d_nodes[0] << ")";
          break;
        }
        case UNBAN: 
        { 
          pretty << "(UNBAN " << d_nodes[0] << ")";
          break;
        }
        case CHECK: 
        {
          pretty << "(CHECK " << d_nodes[0] << " " << d_nodes[1] << ")";
          break;
        }
        case BRANCH: 
        { 
          pretty << "(BRANCH " << d_nodes[0] << " " << d_nodes[1] << ")";
          break;
        }
        case COMBINE: 
        {
          pretty << "(COMBINE " << d_node_kind << " " << d_num_args << ")";
          break;
        }
        default: 
        {
          pretty << "(UNHANDLED)";
          break;
        }
      }
      return pretty.str();
    }
  };

  std::vector<Job> jobs;
  std::vector<Node> results;
  std::unordered_set<Node> ban;
  NodeManager* nm = nodeManager();
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();

  jobs.push_back(Job::makeEval(n));

  while (!jobs.empty() && fuel > 0)
  {
    if (TraceIsOn("evaluateDefinitionsSymbolically"))
    {
      std::ostringstream msg;
      msg << "(state" << std::endl;
      msg << "(jobs" << std::endl;
      for (const Job& job : jobs)
      {
        msg << job.toString() << std::endl;
      }
      msg << ")" << std::endl; // jobs
      msg << "(results" << std::endl;
      for (const Node& result : results)
      {
        msg << result << std::endl;
      }
      msg << ")" << std::endl; // results
      msg << ")" << std::endl; // state
      Trace("evaluateDefinitionsSymbolically") << msg.str();
    }

    --fuel;

    Job j = jobs.back();
    jobs.pop_back();

    switch (j.d_job_kind)
    {
      case EVAL: 
      {
        Node jn = j.d_nodes[0];
        
        if (jn.isConst())
        {
          results.push_back(jn);
        }
        else if (jn.isVar() && jn.getType().isDatatype() && ee->hasTerm(jn))
        {
          bool not_found = true;
          Node eqc_rep = ee->getRepresentative(jn);
          eq::EqClassIterator eqc_it(eqc_rep, ee);
          while (!eqc_it.isFinished() && not_found)
          {
            Node eqc_mem = *eqc_it;
            if (eqc_mem.getKind() == Kind::APPLY_CONSTRUCTOR)
            {
              not_found = false;
              jobs.push_back(Job::makeEval(eqc_mem));
            }
            ++eqc_it;
          }
          if (not_found)
          {
            results.push_back(jn);
          }
        }
        else if (jn.isVar())
        {
          results.push_back(jn);
        }
        else if (jn.getKind() == Kind::ITE)
        {
          jobs.push_back(Job::makeBranch(jn[1], jn[2]));
          jobs.push_back(Job::makeEval(jn[0]));
        }
        else if (jn.getMetaKind() == kind::metakind::OPERATOR)
        {
          jobs.push_back(Job::makeCombine(jn.getKind(), jn.getNumChildren()));
          for (const Node child : jn)
          {
            jobs.push_back(Job::makeEval(child));
          }
        }
        else if (jn.getKind() == Kind::APPLY_SELECTOR)
        {
          results.push_back(rewrite(jn));
        }
        else
        {
          Assert(jn.getMetaKind() == kind::metakind::PARAMETERIZED);
          jobs.push_back(Job::makeCombine(jn.getKind(), jn.getNumChildren() + 1));
          jobs.push_back(Job::makeEval(jn.getOperator()));
          for (const Node child : jn)
          {
            jobs.push_back(Job::makeEval(child));
          }
        }
        break;
      }

      case BAN: 
      {
        Node func_sym = j.d_nodes[0];
        ban.insert(func_sym);
        break;
      }

      case UNBAN:
      {
        Node func_sym = j.d_nodes[0];
        ban.erase(func_sym);
        break;
      }

      case CHECK: 
      {
        Node fallback = j.d_nodes[0];
        Node func_sym = j.d_nodes[1];
        Node cand = results.back();
        results.pop_back();
        bool found_ite = false;
        bool found_func_sym = false;
        NodeDfsIterable cand_iterable(cand);
        NodeDfsIterator cand_it = cand_iterable.begin();
        NodeDfsIterator cand_end = cand_iterable.end();
        while (cand_it != cand_end && !found_ite)
        {
          Node cand_des = *cand_it;
          if (cand_des.getKind() == Kind::ITE)
          {
            found_ite = true;
          }
          else if (cand_des.getKind() == Kind::APPLY_UF
                   && cand_des.getOperator() == func_sym)
          {
            found_func_sym = true;
          }
          ++cand_it;
        }
        if (found_ite)
        {
          results.push_back(fallback);
        }
        else if (found_func_sym)
        {
          jobs.push_back(Job::makeEval(cand));
        }
        else
        {
          results.push_back(cand);
        }
        break;
      }

      case BRANCH: 
      {
        Node test = results.back();
        Node conseq = j.d_nodes[0];
        Node alt = j.d_nodes[1];
        results.pop_back();
        if (test.isConst())
        {
          if (test.getConst<bool>())
          {

            jobs.push_back(Job::makeEval(conseq));
          }
          else
          {
            jobs.push_back(Job::makeEval(alt));
          }
        }
        else
        {
          results.push_back(nm->mkNode(Kind::ITE, test, conseq, alt));
        }
        break;
      }

      case COMBINE: 
      {
        Kind k = j.d_node_kind;
        size_t num_args = j.d_num_args;
        std::vector<Node> children;
        for (size_t i = 0; i < num_args; ++i)
        {
          children.push_back(results.back());
          results.pop_back();
        }
        Node combined = nm->mkNode(k, children);

        if (k != Kind::APPLY_UF)
        {
          // Case (1).
          results.push_back(rewrite(combined));
        }
        else
        {
          Node func_sym = children[0];
          std::map<Node, FunDefInfo>::const_iterator info_it =
              d_funDefMap.find(func_sym);
          if (info_it == d_funDefMap.end())
          {
            // Case (2).
            results.push_back(combined);
          }
          else
          {
            Node par_body = info_it->second.d_body;
            std::vector<Node> formals = info_it->second.d_args;
            std::vector<Node> actuals;
            actuals.insert(actuals.end(), ++children.begin(), children.end());
            Node body = evaluate(par_body, formals, actuals);

            bool symbolic = false;
            for (const Node& actual : actuals)
            {
              NodeDfsIterable actual_iterable(actual);
              NodeDfsIterator actual_it = actual_iterable.begin();
              NodeDfsIterator actual_end = actual_iterable.end();
              while (actual_it != actual_end)
              {
                Node actual_des = *actual_it;
                if (actual_des.isVar())
                {
                  symbolic = true;
                  break;
                }
                ++actual_it;
              }
              if (symbolic)
              {
                break;
              }
            }

            if (!symbolic)
            {
              // Case (3)
              jobs.push_back(Job::makeEval(body));
            }
            else if (ban.find(func_sym) != ban.end())
            {
              // Case (4).
              results.push_back(combined);
            }
            else
            {
              // Case (5).
              jobs.push_back(Job::makeCheck(combined, func_sym));
              jobs.push_back(Job::makeUnban(func_sym));
              jobs.push_back(Job::makeEval(body));
              jobs.push_back(Job::makeBan(func_sym));
            }
          }
        }
        break;
      }

      default:
      {
        break;
      }
    }
  }

  Node result = results.back();
  results.clear();

  return result;
}

bool FunDefEvaluator::hasDefinitions() const { return !d_funDefMap.empty(); }

const std::vector<Node>& FunDefEvaluator::getDefinitions() const
{
  return d_funDefs;
}
Node FunDefEvaluator::getDefinitionFor(Node f) const
{
  std::map<Node, FunDefInfo>::const_iterator it = d_funDefMap.find(f);
  if (it != d_funDefMap.end())
  {
    return it->second.d_quant;
  }
  return Node::null();
}
Node FunDefEvaluator::getLambdaFor(Node f) const
{
  std::map<Node, FunDefInfo>::const_iterator it = d_funDefMap.find(f);
  if (it != d_funDefMap.end())
  {
    NodeManager* nm = nodeManager();
    return nm->mkNode(Kind::LAMBDA,
                      nm->mkNode(Kind::BOUND_VAR_LIST, it->second.d_args),
                      it->second.d_body);
  }
  return Node::null();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
