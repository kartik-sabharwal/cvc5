/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Techniques for evaluating terms with recursively defined functions.
 */

#include "cvc5_private.h"

#ifndef CVC5__QUANTIFIERS_FUN_DEF_EVALUATOR_H
#define CVC5__QUANTIFIERS_FUN_DEF_EVALUATOR_H

#include <map>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/quantifiers_state.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * Techniques for evaluating recursively defined functions.
 */
class FunDefEvaluator : protected EnvObj
{
 private:
  QuantifiersState& d_qstate;
 public:
  FunDefEvaluator(Env& env, QuantifiersState& qs);
  ~FunDefEvaluator() {}
  /**
   * Assert definition of a (recursive) function definition given by quantified
   * formula q.
   * @param q The quantified formula to assert.
   * @return true if we added a definition to this class for q.
   */
  bool assertDefinition(Node q);
  /**
   * Same as above, without asserting.
   * @param q The quantified formula.
   * @return true if a definition could be inferred for q.
   */
  bool isDefinition(const Node& q) const;
  /**
   * Simplify node based on the (recursive) function definitions known by this
   * class. If n cannot be simplified to a constant, then this method returns
   * null.
   */
  Node evaluateDefinitions(Node n) const;
  /*
   * Simplify node based on the (recursive) function definitions known by this
   * class.
   *
   * **Implementation**.
   *
   * When we pop a job from visit, the job stack, we make sure it has a home in
   * visited, the cache.  Let's name the job cur.  If cur is not in visited we
   * associate cur with the null node in visited.  Next we push cur's
   * dependencies on to visit before once again pushing cur on to visit.  When
   * cur is eventually popped off visit again it'll be with the guarantee that
   * its dependencies have been fully evaluated, and that their fully evaluated
   * forms can be retrieved from the cache.  If cur is already in visited its
   * corresponding value is stored in cur_eval, which may be the null node.
   *
   * If cur_eval is the null node that means cur hasn't been evaluated yet
   * though we can expect that its dependencies have been fully evaluated.  We
   * have four important cases to handle: (1) cur has metakind OPERATOR and kind
   * ITE, (2) cur has metakind OPERATOR, (3) cur has metakind PARAMETERIZED and
   * kind APPLY_UF, and (4) cur has metakind PARAMETERIZED.
   *
   * **Jobs**.
   *
   * We will have four kinds of jobs: EVAL(n), BAN(n), UNBAN(n) and CHECK(n0,
   * n1) where each n denotes an instance of Node.  The function
   * evaluateDefinitions() dictates how to handle EVAL(n) in most situations.
   * Special rules apply when Node n has the form f(e) where f is a recursively
   * defined function symbol.  The first time we see EVAL(f(e)) we do the usual
   * tasks: we make a home for f(e) in the cache, push EVAL(f(e)) on to the job
   * stack, and finally push EVAL(e) on to the job stack.  The second time we
   * see EVAL(f(e)) we should grab the full evaluation of e from the cache and
   * call it v.  If v does not contain variables we can simply do as
   * evaluateDefinitions() says.  Otherwise we need to exercise some caution.
   * We ought to check if f is in the ban list.  If it is, we are banned from
   * once-unrolling f in f(v) and must associate f(e) with f(v) in the cache.
   * Say f is absent from the ban list.  Let b[x] denote the body of f(x), b[x]
   * is an expression may contain free occurrences of the variable x.  We add
   * the jobs CHECK(f(e), b[v]), UNBAN(f), EVAL(b[v]), BAN(f) to the job stack
   * in that order.  To handle BAN(f) and we add f to the ban list.  To handle
   * UNBAN(f) we remove f from the ban list.  CHECK(f(e), b[v]) serves as the
   * conclusion to EVAL(f(e)).  To handle it we grab the full evaluation of b[v]
   * from the cache and call it w.  If w is free of Nodes with kind ITE, we
   * associate f(e) with w in the cache.  Otherwise we associate f(e) with f(v).
   *
   * **Unrolling**.
   *
   * Suppose we define addition on the natural numbers by recursion as: for all
   * x, y. plus(x, y) = ite(is-Z(x), y, S(plus(p(x), y))).  Suppose m and n are
   * variable symbols such that m is in the equivalence class {m, S(p(m))} while
   * n is in the equivalence class {n}.  We want plus(m, n) to evaluate to
   * S(plus(p(m), n)) and plus(p(m), n) to evaluate to itself.  On what basis do
   * we determine to unroll the function's definition in the former case but not
   * in the latter case?  Note that a once-unrolling of plus in the former case
   * introduces a conditional expression that we can get rid of.  In the latter
   * case we can't get rid of the conditional introduced by a once-unrolling.
   *
   * It's still possible to confuse this strategy.  Let's define a recognizer
   * for even natural numbers: for all x. even(x) = ite(is-Z(x), true,
   * ite(is-Z(p(x)), false, ite(even(p(p(x))), true, false))).  Assume that
   * ite(even(p(p(x))), true, false) isn't transformed into even(p(p(x))) by
   * cvc5's rewriter.  Suppose we have a variable k in the equivalence class {k,
   * S(p(k))}, p(k) is in the equivalence class {p(k), S(p(p(k)))}, and p(p(k))
   * is in the singleton equivalence class {p(p(k))}.  Under our strategy
   * even(k) should evaluate to itself because even(p(p(k))) in
   * ite(even(p(p(k))), true, false) doesn't evaluate to either true or false.
   * even(p(p(k))) isn't unrolled because we don't want to trigger a chain of
   * _symbolic_ unrollings of one specific function (non-symbolic unrollings are
   * fine).  However if the definition of even were a little simpler: for all
   * x. even(x) = ite(is-Z(x), true, ite(is-Z(p(x)), false, even(p(p(x))))),
   * then even(k) would evaluate to even(p(p(k))).
   *
   * **Dependencies**.
   *
   * The dependencies of a node can be determined from its metakind and kind.  A
   * node with metakind CONSTANT has no dependencies.  Given a node of datatype
   * sort with metakind VARIABLE, any single node in its equivalence class with
   * a constructor as its head symbol can be chosen as its dependency.  If there
   * are no such nodes then the variable is considered fully evaluated.  A node
   * with kind ITE depends on its test expression, which happens to be its first
   * child.  I believe it's fair to assume all other nodes depend on all their
   * arguments (provided they take arguments).
   *
   * **Local variables**.
   *
   * nm is a pointer to the current node manager.  It is used to create new
   * nodes.
   *
   * visited is the cache for the symbolic evaluator.  For any Node n in the
   * domain of visited, visited[n] is either Node::null() or it is the result of
   * fully evaluating n.  Normally a worklist algorithm, like this one,
   * maintains a result stack.  This cache obviates the need for a result stack
   * -- to evaluate f(e), we push f(e) followed by e on the job stack.  e is
   * popped from the stack first, evaluated, and its reduced form is placed in
   * the cache.  Next, f(e) is popped from the stack and f(visited[e]) is placed
   * in the cache.
   *
   * visit is the stack of pending evaluation jobs.  So long as visit is
   * non-empty, visit.back() is next in line to be evaluated.  If visit is empty
   * we're done.
   *
   * cur is short for current job and holds the value of visit.back() in the
   * current iteration of the while loop.
   *
   * curEval is short for 'current job evaluates to' and holds the value of
   * visited[cur] in the current iteration of the while loop.  If it is
   * Node::null() then cur has not been evaluated yet.
   *
   * f stores the head function symbol of the node we are trying to evaluate.
   */
  /**
   * Unlike evaluateDefinitions(), this function does not care to cache
   * intermediate results.  We have separate job and memory stacks as in other
   * worklist algorithms.  We also maintain a mutable set of function symbols
   * that we are not allowed to unroll.
   *
   * The 6 job kinds are EVAL, BAN, UNBAN, CHECK, BRANCH, and COMBINE.  Each job
   * is a struct with 5 fields: a job kind, two nodes, a node kind, and a
   * size_t.  EVAL expects any single node as an argument.  Both BAN and UNBAN
   * expect a single function symbol as an argument.  CHECK expects two
   * arguments.  The first can be any node though the second must be a function
   * symbol.  BRANCH expects any two nodes as arguments.  COMBINE expects a node
   * kind an a size_t.
   *
   * To handle BAN(f) and UNBAN(f) simply add or remove f from the banned set as
   * suggested by the job's kind.
   *
   * To handle CHECK(n, f) pop the top item from the result stack.  Call it r.
   * If r contains a node with kind ITE, we push n on to the result stack.  If r
   * doesn't contain a node with kind ITE but contains at least one occurrence
   * of f, we push EVAL(r) on to the job stack.  If r is free of both ITE nodes
   * and occurrences of f, we push r on to the result stack.
   *
   * To handle BRANCH(th, el) we pop the top element off the result stack.  If
   * it's the cvc5 constant true then we push EVAL(th) on to the job stack
   * otherwise we push EVAL(el) on the job stack.
   *
   * Handling EVAL(n): if n.isConst(), we push n on to the result stack.  If
   * n.isVar(), has datatype sort, and is in the equality engine then we scan
   * its equivalence class for constructor terms.  Pick any one constructor term
   * c that n is equivalent to, then add EVAL(c) to the job stack.  If n is a
   * variable but doesn't meet any of these conditions -- it's not of datatype
   * sort, it's not in the equality engine, or it isn't equivalent to a
   * constructor term -- we push n itself on to the result stack.  If n is a
   * node with kind ITE and form ite(n_0, n_1, n_2), we push BRANCH(n_1, n_2)
   * and EVAL(n_0) on to the job stack, in that order.  If n has metakind
   * OPERATOR, kind k, and m child nodes, then we push COMBINE(k, m), and
   * EVAL(n[0]) through EVAL(n[m-1]) to the job stack.  If n has metakind
   * PARAMETERIZED, kind k, operator f, and m child nodes, then we push
   * COMBINE(k, m+1), EVAL(f), and EVAL(n[0]) through EVAL(n[m-1]) to the job
   * stack.
   *
   * Handling COMBINE(k, m): we pop the first m items off the result stack.  We
   * then create a new node n with kind k and the popped items as its arguments.
   * We split into 5 cases.  Each case assumes that none of its predecessors
   * applies: (1) n is not an application of an uninterpreted function symbol
   * (2) the operator of n is not associated with a definition (3) none of n's
   * children is symbolic (4) unrolling the operator of n is banned (5)
   * otherwise.  If (1) we call the rewriter on n and push the rewritten term on
   * to the result stack.  If (2) we push n itself on to the result stack. If
   * (3) let f denote the operator of n, let x denote the formal parameters of
   * f, and let b[x] denote the body of f.  Recognize that n has the form f(v)
   * where v denotes the actual parameters of f.  Push EVAL(b[v]) on to the job
   * stack.  If (4) push n itself on to the result stack.  If (5) then define f,
   * x, b[x] and v as in case (3).  Push CHECK(n, f), UNBAN(f), EVAL(b[v]) and
   * BAN(f) on to the job stack, in that order.
   *
   * This function uses the following abbreviations.  n for 'node', jn for 'job
   * node', j for 'job', func_sym for 'function symbol', nm for 'node manager',
   * ee for 'equality engine', eqc_rep for 'equivalence class representative',
   * eqc_it for 'equivalence class iterator', eqc_mem for 'equivalence class
   * member', found_ite for 'found node with kind ITE', found_func_app for
   * 'found application of function symbol', cand for 'candidate', cand_iterable
   * for 'iterable constructed from candidate', cand_it for 'iterator over
   * descendants of candidate', cand_end for 'end of range for iterator over
   * descendants of candidate', cand_des for 'descendant of candidate', conseq
   * for 'consequence (then branch) of conditional', alt for 'alternative (else
   * branch) of conditional', k for 'kind', num_args for 'number of arguments',
   * ap for 'application'.
   */
  Node evaluateDefinitionsSymbolically(Node n, size_t fuel) const;
 /**
   * Has a call to assertDefinition been made? If this returns false, then
   * the evaluate method is the same as calling the rewriter, and returning
   * false if the result is non-constant.
   */
  bool hasDefinitions() const;

  /** Get definitions */
  const std::vector<Node>& getDefinitions() const;
  /** Get definition for function symbol f, if it is cached by this class */
  Node getDefinitionFor(Node f) const;
  /** Get lambda for function symbol f, if it is cached by this class */
  Node getLambdaFor(Node f) const;

 private:
  /**
   * If returns true, updates index to the child index of the equality that is
   * the head, i.e. for (forall ((x Int)) (= (f x) t)) we set index to 0, for
   * (forall ((x Int)) (= t (f x))) we set index to 1.
   */
  bool getDefinitionIndex(const Node& q, size_t& index) const;
  /** Add definition head = body, from quantified formula q */
  void addDefinition(const Node& head, const Node& body, const Node& q);
  /** information cached per function definition */
  class FunDefInfo
  {
   public:
    /** the quantified formula */
    Node d_quant;
    /** the body */
    Node d_body;
    /** the formal argument list */
    std::vector<Node> d_args;
  };
  /** maps functions to the above information */
  std::map<Node, FunDefInfo> d_funDefMap;
  /** list of all definitions */
  std::vector<Node> d_funDefs;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
