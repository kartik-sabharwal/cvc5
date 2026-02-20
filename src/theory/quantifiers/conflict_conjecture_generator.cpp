/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Conflict-based conjecture generation
 */

#include "theory/quantifiers/conflict_conjecture_generator.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "expr/subs.h"
#include "expr/dtype_cons.h"
#include "options/quantifiers_options.h"
#include "smt/set_defaults.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/term_pools.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_tuple_enumerator.h"
#include "theory/smt_engine_subsolver.h"
#include "util/random.h"
#include "expr/sygus_grammar.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "expr/sygus_term_enumerator.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"

using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

ConflictConjectureGenerator::ConflictConjectureGenerator(
    Env& env,
    QuantifiersState& qs,
    QuantifiersInferenceManager& qim,
    QuantifiersRegistry& qr,
    TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_funDefEvaluator(env),
      d_conjGen(userContext()),
      d_conjGenIndex(userContext()),
      d_conjGenCache(userContext())
{
  d_switched_off = false;
  d_short_circuited = false;
  d_iuqf_populated = false;
  d_iuqf = std::unordered_set<Node>{};
  d_false = nodeManager()->mkConst(false);
  d_set_up_fun_def_evaluator = false;
  d_banned = std::unordered_set<Node>{};

  d_subOptions.copyValues(options());
  d_subOptions.write_quantifiers().instMaxRounds = 20;
  d_subOptions.write_quantifiers().quantInduction = false;
  d_subOptions.write_quantifiers().dtStcInduction = false;
  d_subOptions.write_quantifiers().conjectureGen = false;
  d_subOptions.write_quantifiers().contextualEnumerator = false;
  d_subOptions.write_quantifiers().conflictConjectureGen = false;
  d_subOptions.write_quantifiers().poolInst = false;
  smt::SetDefaults::disableChecking(d_subOptions);
}

void ConflictConjectureGenerator::presolve() {}

bool ConflictConjectureGenerator::needsCheck(Theory::Effort e)
{
  return e >= Theory::EFFORT_LAST_CALL;
  // return d_qstate.getInstWhenNeedsCheck(e);
  // return true;
  // return !d_qstate.isConflictingInst() && (e == Theory::EFFORT_FULL);
}

void ConflictConjectureGenerator::reset_round(Theory::Effort e) {}

void ConflictConjectureGenerator::registerQuantifier(Node q) {}

void ConflictConjectureGenerator::checkOwnership(Node q) {}

QuantifiersModule::QEffort ConflictConjectureGenerator::needsModel(
    Theory::Effort e)
{
  return QEFFORT_STANDARD;
}

/* This function is supposed to add the following formula as a pending lemma.
 *
 *     let phi = forall x, y, z. plus(x, plus(y, z)) = plus(z, plus(x, y))
 *     in or(phi, not(phi))
 *
 * It also adds the following as a pending phase requirement.
 *
 *     not(phi)
 *
 * We should be able to immediately solve the times-right-dist.smt2 with this
 * combination.
 *
 * To do this, we need to:
 *
 * 0.  Grab the type node for the natural number sort.
 * 1.  Construct bound variable symbols for 'x', 'y', and 'z'.
 * 2.  Find the symbol for 'plus'.
 * 3.  Construct 'phi'.
 * 4.  Construct 'lem', the disjunction of phi with its negation.
 * 5.  Add 'lem' as a pending lemma.
 * 6.  Add 'phi' with 'false' as a pending phase requirement.
 *
 * The way to look at the entire list of function symbols is to use
 * `getTermDatabase()`, `getNumOperators()` and `getOperator()`.  The way to
 * create bound variables is to use `NodeManager::mkBoundVar()`.  You will also
 * need the kinds `APPLY_UF`, `BOUND_VAR_LIST`, and `FORALL`.  You will need
 * `nodeManager()`, `mkNode()`, `negate()`, `eqNode()`, `orNode()`.  To send the
 * lemma you'll need the member functions `addPendingLemma()` and
 * `addPendingPhaseRequiement()` and the field `d_qim`.
 */
void ConflictConjectureGenerator::shortCircuit()
{
  Node plus = Node::null();
  Node succ = Node::null();

  // Search for the first operator with the name "plus".
  {
    // term_db --> term database.
    TermDb* term_db = getTermDatabase();

    // n_ops --> number of operators.
    const size_t n_ops = term_db->getNumOperators();

    // i --> operator index.
    for (size_t i = 0; i < n_ops; ++i)
    {
      // op --> i th operator.
      const Node op = term_db->getOperator(i);

      if (op.getName() == "plus" && plus.isNull())
      {
        plus = op;
      }

      if (op.getName() == "S" && succ.isNull())
      {
        succ = op;
      }
    }
  }

  // We expect the the range type of `plus` is the natural number datatype.
  // nat_ty --> natural number type.
  const TypeNode nat_ty = plus.getType().getRangeType();

  // Create three bound variables of the natural number datatype.
  // const Node x = NodeManager::mkBoundVar("x", nat_ty);
  // const Node y = NodeManager::mkBoundVar("y", nat_ty);
  // const Node z = NodeManager::mkBoundVar("z", nat_ty);

  // Grab a pointer to the current NodeManager instance.
  NodeManager* node_mgr = nodeManager();

  // Construct the formula
  //
  // (forall ((N1 Nat) (N0 Nat) (N2 Nat))
  //   (= (S (plus (S N0) (plus N1 N2)))
  //      (plus (S N1) (S (plus N0 N2)))))
  //
  // Define the body as follows.
  //
  // e0 := e1 = e2
  // e1 := S(e3)
  // e3 := plus(e4, e5)
  // e4 := S(n0)
  // e5 := plus(n1, n2)
  // e2 := plus(e6, e7)
  // e6 := S(n1)
  // e7 := S(e8)
  // e8 := plus(n0, n2)
  // bvs := [n1, n0, n2]
  // phi := forall bvs. e0
  // lem := phi or not(phi)

  const Node n0 = NodeManager::mkBoundVar("x", nat_ty);
  const Node n1 = NodeManager::mkBoundVar("y", nat_ty);
  const Node n2 = NodeManager::mkBoundVar("z", nat_ty);
  const Node e8 = node_mgr->mkNode(Kind::APPLY_UF, std::vector<Node>{plus, n0, n2});
  const Node e7 = node_mgr->mkNode(Kind::APPLY_CONSTRUCTOR, std::vector<Node>{succ, e8});
  const Node e6 = node_mgr->mkNode(Kind::APPLY_CONSTRUCTOR, std::vector<Node>{succ, n1});
  const Node e2 = node_mgr->mkNode(Kind::APPLY_UF, std::vector<Node>{plus, e6, e7});
  const Node e5 = node_mgr->mkNode(Kind::APPLY_UF, std::vector<Node>{plus, n1, n2});
  const Node e4 = node_mgr->mkNode(Kind::APPLY_CONSTRUCTOR, std::vector<Node>{succ, n0});
  const Node e3 = node_mgr->mkNode(Kind::APPLY_UF, std::vector<Node>{plus, e4, e5});
  const Node e1 = node_mgr->mkNode(Kind::APPLY_CONSTRUCTOR, std::vector<Node>{succ, e3});
  const Node e0 = node_mgr->mkNode(Kind::EQUAL, std::vector<Node>{e1, e2});
  const Node bvs = node_mgr->mkNode(Kind::BOUND_VAR_LIST, std::vector<Node>{n1, n0, n2});
  const Node phi = node_mgr->mkNode(Kind::FORALL, bvs, e0);

  // (forall ((n0 Nat) (n1 Nat) (n2 Nat))
  //   (= (plus n0 (plus n1 n2)) (plus n1 (plus n0 n2))))
  //
  // g0 := g1 = g2
  // g1 := plus(n0, g3)
  // g3 := plus(n1, n2)
  // g2 := plus(n1, g4)
  // g4 := plus(n0, n2)
  // alt_bvs := [n0, n1, n2]
  // psi := forall bvs. g0
  // alt_lem := phi or not(phi)
  
  const Node g4 = node_mgr->mkNode(Kind::APPLY_UF, std::vector<Node>{plus, n0, n2});
  const Node g2 = node_mgr->mkNode(Kind::APPLY_UF, std::vector<Node>{plus, n1, g4});
  const Node g3 = node_mgr->mkNode(Kind::APPLY_UF, std::vector<Node>{plus, n1, n2});
  const Node g1 = node_mgr->mkNode(Kind::APPLY_UF, std::vector<Node>{plus, n0, g3});
  const Node g0 = node_mgr->mkNode(Kind::EQUAL, std::vector<Node>{g1, g2});
  const Node alt_bvs = node_mgr->mkNode(Kind::BOUND_VAR_LIST, std::vector<Node>{n0, n1, n2});
  const Node psi = node_mgr->mkNode(Kind::FORALL, alt_bvs, g0);

  // Ask the user which lemma should be sent to the solver.
  Node choice = Node::null();
  std::cout << "Which conjecture should the short-circuiting function send?" << std::endl << "1. " << phi << std::endl << "2. " << psi << std::endl << "[1/2]: ";
  {
    std::string resp;
    std::getline(std::cin, resp);
    Assert(resp.size() > 0);
    if (resp[0] == '1')
    {
      choice = phi;
    }
    else if (resp[0] == '2')
    {
      choice = psi;
    }
  }
  // Make sure the user has actually chosen something.
  Assert(!choice.isNull());

  // Now let's ask the user if they want to send just the positive version of
  // the lemma, or just send its negation.  Needless to say this is unsound.
  // The third option is to send the full splitting lemma, which is sound.
  std::cout << "What should we do?" << std::endl << "[0: Assume conjecture | 1: Prove conjecture | 2: Send splitting lemma] ";
  {
    std::string resp;
    std::getline(std::cin, resp);
    if (resp.size() > 0 && resp[0] == '0')
    {
    }
    else if (resp.size() > 0 && resp[0] == '1')
    {
      choice = choice.negate();
    }
    else if (resp.size() > 0 && resp[0] == '2')
    {
      choice = choice.orNode(choice.negate());
    }
    else
    {
      Assert(false);
    }
  }
  std::cout << "Sending " << choice << std::endl;

  // const Node lem = choice.orNode(choice.negate());
  d_qim.addPendingLemma(choice, InferenceId::QUANTIFIERS_CONFLICT_CONJ_GEN_SPLIT);
  // d_qim.addPendingPhaseRequirement(choice, false);

  // Let's 'remember' that we've called `shortCircuit()` once.  We don't need to call it multiple times.
  d_short_circuited = true;

  return;
}

void ConflictConjectureGenerator::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e != QEFFORT_STANDARD)
  {
    return;
  }

  quantifiers::FirstOrderModel* model = d_treg.getModel();

  if (d_switched_off)
  {
    return;
  }

  // If `d_iuqf` hasn't been populated, populate it.
  if (d_iuqf_populated)
  {
    // Go over all universally quantified formulas and print the ones that aren't in `d_iuqf`.
    // std::ofstream& inference_stream = *d_env.getInferenceStream();
    // inference_stream << "(new-quantified-formulas";
    // n_aqfs is 'number of asserted quantified formulas'.
    size_t naq = model->getNumAssertedQuantifiers();
    for (size_t i = 0; i < naq; i++)
    {
      Node phi = model->getAssertedQuantifier(i);

      // is_phi_init is 'is phi in the initial set of  universally quantified formulas?'
      bool is_phi_init = d_iuqf.find(phi) != d_iuqf.end();

      if (!is_phi_init)
      {
        // inference_stream << std::endl << phi;
      }
    }
    // inference_stream << std::endl << ")" << std::endl;
  }
  else
  {
    size_t naq = model->getNumAssertedQuantifiers();
    for (size_t i = 0; i < naq; i++)
    {
      Node phi = model->getAssertedQuantifier(i);
      d_iuqf.insert(phi);
    }

    d_iuqf_populated = true;
  }

  Trace("cconjGen") << "(list " << std::endl;

  // I am not going to set up the evaluator because I will not rely on it during
  // evaluation.  I will employ the e-matching based filter instead.

  // if (!d_set_up_fun_def_evaluator)
  // {
  //   setUpFunDefEvaluator();
  // }

  Trace("ccgen-debug") << "Refresh function definitions..." << std::endl;
  std::unordered_set<Node> qsyms;
  std::unordered_set<TNode> qvisited;
  for (size_t i = 0; i < model->getNumAssertedQuantifiers(); i++)
  {
    Node phi = model->getAssertedQuantifier(i);
    Trace("ccgen-debug") << "- quant : " << phi << std::endl;

    // record symbols
    expr::getSymbols(phi, qsyms, qvisited);
  }

  d_ee = d_qstate.getEqualityEngine();
  d_eqcGen.clear();
  d_eqcGenRec.clear();
  std::vector<Node> candDeq;
  eq::EqClassIterator eqc = eq::EqClassIterator(d_false, d_ee);
  Trace("cconjGen") << "(list" << std::endl << "\"disequalities\"" << std::endl;
  while (!eqc.isFinished())
  {
    Node n = *eqc;
    if (n.getKind() == Kind::EQUAL)
    {
      Trace("cconjGen") << "(quote " << n << ")" << std::endl;
      candDeq.push_back(n);
    }
    ++eqc;
  }
  Trace("cconjGen") << ")" << std::endl;

  Trace("cconjGen") << "(list " << std::endl << "\"kept disequalities\"" << std::endl;
  for (const Node& eq : candDeq)
  {
    Trace("ccgen-debug") << "- disequality: " << eq << std::endl;
    std::unordered_set<Node> lhs_syms;
    expr::getSymbols(eq[0], lhs_syms);
    std::unordered_set<Node> rhs_syms;
    expr::getSymbols(eq[1], rhs_syms);
    std::unordered_set<Node> syms;
    syms.insert(lhs_syms.begin(), lhs_syms.end());
    syms.insert(rhs_syms.begin(), rhs_syms.end());
    const bool lhs_has_skolem = std::any_of(lhs_syms.begin(), lhs_syms.end(), [](TNode n){ return n.getKind() == Kind::SKOLEM; });
    const bool rhs_has_skolem = std::any_of(rhs_syms.begin(), rhs_syms.end(), [](TNode n){ return n.getKind() == Kind::SKOLEM; });
    const bool eq_has_func_sym = std::any_of(syms.begin(), syms.end(), [](TNode n){ return n.isVar(); });
    if (!lhs_has_skolem || !rhs_has_skolem || !eq_has_func_sym)
    {
      Trace("ccgen-debug") << "...filter " << eq << std::endl;
      continue;
    }
    Trace("ccgen-debug1") << "Disequality " << eq << " has symbols " << syms << std::endl;
    Subs ss;
    for (const Node& s : syms)
    {
      if (!s.getType().isFirstClass())
      {
        continue;
      }
      // if the symbol appears in a quantified formula, do not trust its model
      // value. HACK: Also always take model values for skolems.
      if (qsyms.find(s) == qsyms.end() || s.getKind() == Kind::SKOLEM)
      {
        Node sm = model->getValue(s);
        Trace("ccgen-debug") << "  - " << s << " = " << sm << std::endl;
        ss.add(s, sm);
      }
    }
    Node eqm = rewrite(ss.apply(eq));
    Trace("ccgen-debug") << "  ...concretizes to " << eqm << std::endl;
    if (eqm == d_false)
    {
      Trace("ccgen-debug") << "...filter " << eq << std::endl;
      continue;
    }
    Trace("ccgen-debug") << "...keep " << eq << std::endl;
    Trace("cconjGen") << "(quote " << eq << ")" << std::endl;
    checkDisequality(eq);
  }
  Trace("cconjGen") << ")" << std::endl;

  Trace("cconjGen") << "(list " << std::endl << "\"send\"" << std::endl;
  // candidate conjectures
  NodeManager* nm = nodeManager();
  while (d_conjGenIndex.get() < d_conjGen.size())
  {
    Node lem = d_conjGen[d_conjGenIndex.get()];
    std::unordered_set<Node> fvs;
    expr::getFreeVariables(lem, fvs);
    std::vector<Node> bvs(fvs.begin(), fvs.end());
    if (!bvs.empty())
    {
      lem =
          nm->mkNode(Kind::FORALL, nm->mkNode(Kind::BOUND_VAR_LIST, bvs), lem);
    }
    d_currConjectures.push_back(lem);
    const Node case_split = nm->mkNode(Kind::OR, lem.negate(), lem);
    Trace("ccgen-lemma") << "ConflictConjectureGenerator: send lemma " << case_split
                         << std::endl;
    d_qim.addPendingLemma(case_split, InferenceId::QUANTIFIERS_CONFLICT_CONJ_GEN_SPLIT);

    // Setting this module as the owner of `lem` should stop other quantifiers modules from attempting to instantiate it.
    d_qreg.setOwner(lem, this);

    // We need to try a proof by induction.  So we do the following to trigger
    // skolemization with inductive strengthening.
    d_qim.addPendingPhaseRequirement(lem, false);

    d_conjGenIndex = d_conjGenIndex.get() + 1;

    Trace("cconjGen") << "(quote " << lem << ")" << std::endl;
  }
  Trace("cconjGen") << ")" << std::endl;

  Trace("cconjGen") << ") " << std::endl;
}

void ConflictConjectureGenerator::buildGrammarFromContext()
{
  // This stores the current interpretation of each variable symbol and each
  // function symbol.
  quantifiers::FirstOrderModel* mdl = d_treg.getModel();

  // These are all the function symbols that *might* be recursively defined.  If
  // there is any doubt we choose to err on the side of caution.
  const std::unordered_set<Node> rec_fun_syms = collectRecursivelyDefinedFunctionSymbols(mdl);

  // Let's print REC_FUN_SYMS to make sure we're captured the right function symbols.
  // {
  //   Trace("build-grammar-from-context") << "rec_fun_syms = {";
  //   bool first_time = true;
  //   for (const Node& sym : rec_fun_syms)
  //   {
  //     if (first_time)
  //     {
  //       first_time = false;
  //     }
  //     else
  //     {
  //       Trace("build-grammar-from-context") << ", ";
  //     }

  //     Trace("build-grammar-from-context") << sym;
  //   }
  //   Trace("build-grammar-from-context") << "}" << std::endl;
  // }

  // We'll use this to store the equalities in the equivalence class of false.
  std::vector<Node> assm_false_eqns;

  // The equality engine.
  eq::EqualityEngine* eq_eng = d_qstate.getEqualityEngine();

  // cvc5's internal representation of the literal 'false'.
  const Node& false_node = nodeManager()->mkConst(false);

  // An iterator that yields all terms in the equivalence class of false.
  eq::EqClassIterator false_it = eq::EqClassIterator(false_node, eq_eng);

  while (! false_it.isFinished())
  {
    // A term that is equivalent to false.
    Node false_term = *false_it;

    // Is the term an equality?
    if (false_term.getKind() == Kind::EQUAL)
    {
      // If so, add it to assm_false_eqns.
      assm_false_eqns.push_back(false_term);
    }

    // Move on to the next term in the equivalence class.
    ++false_it;
  }

  // Let's print the contents of assm_false_eqns.
  // Trace("build-grammar-from-context") << "Equalities in the equivalence class of false are: " << std::endl;
  // for (const Node& assm_false_eqn : assm_false_eqns)
  // {
  //   Trace("build-grammar-from-context") << "- " << assm_false_eqn << std::endl;
  // }

  // We'll concretize the terms in assm_false_eqns using their model values.

  // At the moment let's go over all the assumed-false equalities and print
  // the symbols that occur in them.  Once we have that, we can decide which
  // symbols need to be replaced with their model values.
  Trace("build-grammar-from-context")
  << "The following equalities are asserted false:" << std::endl;
  for (const Node& assm_fls_eqn : assm_false_eqns)
  {
    Trace("build-grammar-from-context") << "** next **" << std::endl;
    Trace("build-grammar-from-context") << "** abstract **" << std::endl;
    Trace("build-grammar-from-context") << assm_fls_eqn << std::endl;
    Trace("build-grammar-from-context") << "** concrete **" << std::endl;
    // We intend to construct the concrete version of ASSM_FALSE_EQN by applying
    // a substitution over all the symbols that occur in ASSM_FALSE_EQN.  The
    // domain of this substitution is the set of symbols in ASSM_FALSE_EQN. Each
    // element in the domain is mapped to its model value in MDL.
    // CONCRETIZER will hold the substitution that concretizes ASSM_FALSE_EQN.
    Subs concretizer;
    // SYMS is a set that will be populated with the domain of CONCRETIZER.
    std::unordered_set<Node> syms;
    // The following statement actually populates SYMS.
    expr::getSymbols(assm_fls_eqn, syms);
    // The following loop populates CONCRETIZER.
    {
      Trace("build-grammar-from-context") << "Leaving symbols {";
      // Is it the first time we're printing a symbol in the following loop?
      bool first_time = true;
      for (const Node& sym : syms)
      {
        const TypeNode& sym_typ = sym.getType();

        // cvc5 is liable to crash if we attempt to fetch the model value of a
        // term whose type is not 'first class'.  Constructor terms are not
        // 'first class'.
        if (sym_typ.isFirstClass())
        {
          // It is misleading to get the model value of a recursively-defined
          // function because its model value will satisfy just the instances of
          // the definition that are currently in scope.
          if (rec_fun_syms.find(sym) == rec_fun_syms.end())
          {
            concretizer.add(sym, mdl->getValue(sym));
          }
        }
        else
        {
          if (first_time)
          {
            first_time = false;
          }
          else
          {
            Trace("build-grammar-from-context") << ", ";
          }
          Trace("build-grammar-from-context") << sym;
        }
      }
    }
    Trace("build-grammar-from-context") << "} ... ";

    // CONCR_ASSM_FALSE_EQN as the name suggests is the concrete version of
    // ASSM_FALSE_EQN.  We also rewrite the result of the substitution because
    // Andy did it in the last iteration of the conjecture generator.
    const Node& concr_assm_fls_eqn = rewrite(concretizer.apply(assm_fls_eqn));

    Trace("build-grammar-from-context") << concr_assm_fls_eqn << std::endl;

    // If the disequality concretizes to false i.e. CONCR_ASSM_FLS_EQN is the
    // same as FALSE_NODE then we throw it away because we don't expect to
    // derive a useful conjecture from it.  On the other hand if it doesn't
    // concretize to false it might actually be entailed (inductively or
    // otherwise).  If we suspect that it is entailed we will conjecture a more
    // general version and try to prove it by induction.  To investigate,
    // we will run CONCR_ASSM_FLS_EQN through checkDisequality().
    if (concr_assm_fls_eqn == false_node)
    {
      continue;
    }
    else
    {
      checkDisequality(concr_assm_fls_eqn);
    }
  }
}

const std::unordered_set<Node> ConflictConjectureGenerator::collectRecursivelyDefinedFunctionSymbols(quantifiers::FirstOrderModel* mdl)
{
  // If we find a function symbol that we believe might be recursively defined
  // we'll add it to this vector.
  std::unordered_set<Node> rec_fun_syms;

  // Let's run through the list of universally quantified formulas and list
  // patterns that might help us identify definitions of recursive functions.
  // Turns out we're looking for universally quantified formulas of the form
  // (forall X, lhs[X] = rhs[X]) where one of lhs[X] or rhs[X] contains some
  // function symbol 'f' at the root of its syntax tree and the other side's
  // expression simply mentions 'f' somewhere.
  {
    // Trace("collect-recursive") << "Asserted universally quantified formulas are:" << std::endl;

    const size_t n = mdl->getNumAssertedQuantifiers();

    for (size_t i = 0; i < n; i++)
    {
      // The I th asserted universally quantified formula.
      const Node& fla = mdl->getAssertedQuantifier(i);

      // Let's print it.
      // Trace("collect-recursive") << fla << std::endl;

      // The body of the aforementioned formula.
      const Node& body = fla[1];

      // We are only interested in a formula if its body is an equality.
      if (body.getKind() == Kind::EQUAL)
      {
        // Does the body fit the shape of a recursive definition?  To start with
        // let's assume it doesn't.  We can correct the assumption later.
        Node rec_fun_sym = Node::null();

        // We do one iteration of the loop from the perspective of the right
        // hand side of the equality and one iteration from the perspective of
        // the left hand side.
        for (const size_t side : {0, 1})
        {
          // If REC_FUN_SYM is non-null we already have what we came for so we
          // do nothing in the loop body.
          if (!rec_fun_sym.isNull())
          {
            continue;
          }
          else
          {
            // When SIDE is 0, SAME is the lhs and OTHER is the rhs.  When SIDE is
            // 1 it's the other way around.
            const Node& same = body[side];
            const Node& other = body[side == 0 ? 1 : 0];

            // Is SAME an application of an uninterpreted function?
            if (same.getKind() == Kind::APPLY_UF)
            {
              // It is!  Let's grab the function symbol for use in the next
              // query.
              const Node& fun_sym = same.getOperator();

              // Let's also grab all the symbols that appear in OTHER.
              std::unordered_set<Node> other_syms;
              expr::getSymbols(other, other_syms);

              // {
              //   Trace("build-grammar-from-context")
              //   << "fun_sym is " << fun_sym << ", while other_syms is {";
              //   bool first_time = true;
              //   for (const Node& sym : other_syms)
              //   {
              //     if (first_time)
              //     {
              //       first_time = false;
              //     }
              //     else
              //     {
              //       Trace("build-grammar-from-context") << ", ";
              //     }

              //     Trace("build-grammar-from-context") << sym;
              //   }
              //   Trace("build-grammar-from-context") << "}" << std::endl;
              // }

              // If FUN_SYM appears in OTHER_SYMS, the current assertion is
              // likely part of a recursive definition.
              if (other_syms.find(fun_sym) != other_syms.end())
              {
                rec_fun_sym = fun_sym;
              }
            }
          }
        }

        // We presume that if the body fits the shape of a recursive definition
        // then we've set REC_FUN_SYM to be non-null.  If it is non-null we
        // should add it to the list of recursive function symbols.
        if (!rec_fun_sym.isNull())
        {
          rec_fun_syms.insert(rec_fun_sym);
        }
      }
    }
  }

  // Trace("collect-recursive") << std::endl;

  return rec_fun_syms;
}

std::string ConflictConjectureGenerator::identify() const
{
  return "conflict-conjecture-gen";
}

void ConflictConjectureGenerator::checkDisequality(const Node& eq)
{
  d_conjBuffer.clear();
  Trace("ccgen1") << "checkDisequality " << eq << std::endl;
  std::vector<Node> vars;
  for (size_t i = 0; i < 2; i++)
  {
    Node r = d_ee->getRepresentative(eq[i]);
    Node v = getOrMkVarForEqc(r);
    vars.push_back(v);
    Trace("cconjGen") << "(list " << std::endl << "\"" << (i == 0 ? "lhs" : "rhs") << " expansions\"" << std::endl;
    getGeneralizations(v);
    Trace("cconjGen") << ")" << std::endl;
  }

  if (TraceIsOn("ConflictConjectureGenerator::equality-engine"))
  {
    d_qstate.debugPrintEqualityEngine("ConflictConjectureGenerator::equality-engine");
    Trace("ConflictConjectureGenerator::equality-engine") << std::endl;
  }

  if (TraceIsOn("ConflictConjectureGenerator::d_bv"))
  {
    Trace("ConflictConjectureGenerator::d_bv") << "(d_bv";
    for (const std::pair<Node, Node> entry : d_bv)
    {
      Trace("ConflictConjectureGenerator::d_bv") << std::endl << std::get<0>(entry) << " -> " << std::get<1>(entry);
    }
    Trace("ConflictConjectureGenerator::d_bv") << ")" << std::endl;
  }

  // if (TraceIsOn("ConflictConjectureGenerator::d_eqcGenRec"))
  // {
  //   Trace("ConflictConjectureGenerator::d_eqcGenRec") << "(d_eqcGenRec";
  //   for (const std::pair<Node, std::vector<Node>> entry : d_eqcGenRec)
  //   {
  //     Trace("ConflictConjectureGenerator::d_eqcGenRec") << std::endl << "(" << std::get<0>(entry) << " (";
  //     for (const Node& gen : std::get<1>(entry))
  //     {
  //       Trace("ConflictConjectureGenerator::d_eqcGenRec") << " " << gen;
  //     }
  //     Trace("ConflictConjectureGenerator::d_eqcGenRec") << "))";
  //   }
  //   Trace("ConflictConjectureGenerator::d_eqcGenRec") << ")" << std::endl;
  // }

  // Print the entirety of the generalization trie.
  if (TraceIsOn("ConflictConjectureGenerator::d_gtrie"))
  {
    debugPrintGenTrie(d_gtrie);
  }

  // see if any generalization of the right hand
  std::vector<Node>& genRhs = d_eqcGenRec[vars[1]];

  Trace("ccgen") << "- look at " << genRhs.size()
                 << " recursive generalizations of RHS" << std::endl;

  Trace("cconjGen") << "(list " << std::endl << "\"compatible\"" << std::endl;
  // generate the candidates, store in d_conjBuffer
  for (const Node& g : genRhs)
  {
    const std::vector<Node>& gfvs = d_genToFv[g];
    Trace("ccgen-debug") << "  - " << g << std::endl;
    // State s = gfvs.empty() ? State::SUBSET : State::UNKNOWN;
    Trace("cconjGen") << "(list " << std::endl << "(list \"rhs\" " << "(quote " << g << "))" << std::endl;
    findCompatible(g, gfvs, vars[0], &d_gtrie, std::vector<Node>{}, 0, State::SUBSET);
    Trace("cconjGen") << ")" << std::endl;
  }
  Trace("cconjGen") << ")" << std::endl;

  findCongruenceCandidates();

  if (TraceIsOn("ConflictConjectureGenerator::d_conjBuffer"))
  {
    Trace("ConflictConjectureGenerator::d_conjBuffer") << "(d_conjBuffer";
    for (const Node& buf_conj : d_conjBuffer)
    {
      Trace("ConflictConjectureGenerator::d_conjBuffer") << std::endl << buf_conj;
    }
    Trace("ConflictConjectureGenerator::d_conjBuffer") << ")" << std::endl;
  }

  // go back and see if the conjectures should be filtered
  for (const Node& lem : d_conjBuffer)
  {
    // canonize it, which catches duplicates modulo alpha equivalence
    Node clem = d_tc.getCanonicalTerm(lem);
    if (filterConjecture(clem))
    {
      continue;
    }
    d_conjGenCache.insert(clem);
    Trace("cconj") << "*** Conjecture : " << clem[0] << " == " << clem[1]
                   << std::endl;
    d_conjGen.emplace_back(lem);
  }

  // Remove this as soon as you can.
  {
    Trace("cconj-filter") << "Have " << d_qim.numPendingLemmas()
                          << " pending lemmas" << std::endl;
    d_qim.doPendingLemmas();
  }
}

Node ConflictConjectureGenerator::getOrMkVarForEqc(const Node& e)
{
  Assert(d_ee->getRepresentative(e) == e);
  std::map<Node, Node>::iterator it = d_bv.find(e);
  if (it != d_bv.end())
  {
    return it->second;
  }
  Node v = NodeManager::mkBoundVar(e.getType());
  d_bv[e] = v;
  d_bvToEqc[v] = e;
  return v;
}

const std::vector<Node>& ConflictConjectureGenerator::getGenForEqc(
    const Node& e)
{
  std::map<Node, std::vector<Node>>::iterator it = d_eqcGen.find(e);
  if (it != d_eqcGen.end())
  {
    return it->second;
  }
  TermDb* tdb = getTermDatabase();
  NodeManager* nm = nodeManager();
  std::vector<Node>& cg = d_eqcGen[e];
  Assert(d_ee->hasTerm(e));
  Assert(d_ee->getRepresentative(e) == e);
  eq::EqClassIterator eqc = eq::EqClassIterator(e, d_ee);
  while (!eqc.isFinished())
  {
    Node n = *eqc;
    ++eqc;
    if (n.getKind() == Kind::APPLY_UF || n.getKind() == Kind::APPLY_CONSTRUCTOR)
    {
      if (n.getNumChildren() == 0)
      {
        cg.emplace_back(n);
        continue;
      }
      // minor optimization: if the term is inactive (e.g. congruent to another
      // term), skip.
      if (!tdb->isTermActive(n))
      {
        continue;
      }
      Node op = n.getOperator();
      std::vector<Node> children;
      children.push_back(op);
      for (const Node& nc : n)
      {
        Assert(d_ee->hasTerm(nc));
        Node r = d_ee->getRepresentative(nc);
        Node v = getOrMkVarForEqc(r);
        children.push_back(v);
      }
      Node gen = nm->mkNode(n.getKind(), children);
      cg.emplace_back(gen);
    }
  }
  return cg;
}

void ConflictConjectureGenerator::getGeneralizations(const Node& v)
{
  if (TraceIsOn("ccgen-terms"))
  {
    Trace("ccgen-terms") << "d_bv is" << std::endl;
    for (std::map<Node, Node>::iterator entry = d_bv.begin();
         entry != d_bv.end();
         entry++)
    {
      Trace("ccgen-terms") << "* " << entry->first << " -> " << entry->second
                           << std::endl;
    }
  }

  Assert(v.getKind() == Kind::BOUND_VARIABLE);
  if (d_eqcGenRec.find(v) != d_eqcGenRec.end())
  {
    return;
  }
  d_eqcGenRec[v].emplace_back(v);
  // base case: own free variable
  addGeneralizationTerm(v, v, 0, {v});
  size_t reps = options().quantifiers.ccgenExpandReps;
  Trace("ccgen-debug") << "Get " << reps << " runs for generalizations of " << v
                       << std::endl;
  for (size_t i = 0; i < reps; i++)
  {
    getGeneralizationsInternal(v);
  }
}

void ConflictConjectureGenerator::getGeneralizationsInternal(const Node& v)
{
  // To make this definition more readable replace all occurrences of the word
  // 'generalization' with 'expansion'.

  // Recall that this class maintains a bijection between a subset of all
  // equivalence class representatives and a set of variables in d_bv and
  // d_bvToEqc.  For any equivalence class representative r that has a mapping
  // in d_bv we must have d_bvToEqc[d_bv[r]] == r.  This function assumes that
  // the input v is the image of some equivalence class representative under
  // d_bv.  Let's call such variables 'equivalence class variables'.  To use our
  // new terminology, this function assumes that its input is an equivalence
  // class variable.

  // We can think of this function as performing a random walk in a graph over
  // terms and adding the vertices visited to the vector referenced by `grecs`.
  // The vertices in this graph are terms built with the equivalence class
  // variables and function-like symbols in the signature (user-declared
  // function symbols and constructor symbols).  Let s and t be two vertices in
  // this graph.  There is an edge between s and t if the following conditions
  // are met.
  //
  // 1.  There is an equivalence class variable x that occurs in s, in other
  // words s can be written as s[x], and
  //
  // 2.  t is s[f(Y)] where f is either a user-declared function symbol or a
  // constructor symbol and Y is a possibly empty sequence of equivalence class
  // variables.
  //
  // 3.  The equivalence class of d_bvToEqc[x] contains the term
  // f(map(d_bvToEqc, Y)) where map(d_bvToEqc, Y) denotes the sequence of terms
  // obtained from looking up each element in Y in d_bvToEqc.
  //
  // In fact we can describe other relevant functions and variables in the
  // context of this random walk.  For any equivalence class variable x, the
  // getGenForEqc(x) returns the vertices that are reachable from x in one step
  // (x's neighbors in the graph).  The field d_eqcGen serves as a cache for
  // getGenForEqc().  On the other hand the vector d_eqcGenRec[x] stores a
  // subset of the vertices that are reachable from x.  We may also view it as
  // an approximation of all the vertices that are reachable from x.  From this
  // perspective, getGeneralizationsInternal(v) attempts to make d_eqcGenRec[v]
  // a better approximation of all vertices reachable from v by adding new
  // vertices.

  // This is the number of expansions we will perform.  Since performing such an
  // expansion is equivalent to taking one step in the random walk, it can be
  // seen as the intended length of our random walk.
  size_t depth = 10;

  // The vertex we are currently at in the random walk.  It's initially v
  // because our random walk starts at v.
  Node cur = v;

  // To take another step in our random walk we can substitute any equivalence
  // class variable that occurs in cur with one of its expansions.  fvs is
  // intended to keep track of all the equivalence class variables that occur in
  // cur.
  std::vector<Node> fvs = {v};

  // grecs is our current best approximation of all the vertices that are
  // reachable from the input equivalence class vertex v.  We hope to improve
  // our approximation by adding all of the vertices visited by our random walk.
  std::vector<Node>& grecs = d_eqcGenRec[v];

  // subs will record the equivalence class variables we have picked to expand
  // during our random walk as well as the expansions we have chosen.  We can
  // think of it as a summary of the walk itself.
  //
  // **Note**.  By choosing to represent our walk as a substitution we force
  // ourselves to expand an equivalence class variable the same way each time we
  // encounter it.  It might be worth exploring a random walk strategy that
  // allows us to expand an equivalence class variable differently each time we
  // see it.
  Subs subs;

  // We elect to expand fvs[rindex].
  size_t rindex = Random::getRandom().pick(0, fvs.size() - 1);

  // One iteration of this loop for each step we intend to take in our random
  // walk.
  for (size_t i = 0; i < depth; i++)
  {
    // This is the equivalence class variable we have elected to expand.
    Node vc = fvs[rindex];

    // Let's print our choice.
    Trace("ccgen-debug-expand") << "process " << vc << std::endl;

    // Trace("getGeneralizationsInternal") << "(list \"d_bvToEqc\"";
    // for (const std::pair<const Node, Node>& entry : d_bvToEqc)
    // {
    //   Trace("getGeneralizationsInternal") << " (list " << std::get<0>(entry) << " " << std::get<1>(entry) << ")";
    // }
    // Trace("getGeneralizationsInternal") << "\"vc\"" << " " << vc << ")";

    // Before we try to expand vc let's ensure that it's truly an equivalence
    // class variable!
    Assert(d_bvToEqc.find(vc) != d_bvToEqc.end());

    // These are vc's expansions.  They can also be described as vc's immediate
    // neighbors in the graph.
    const std::vector<Node>& gens = getGenForEqc(d_bvToEqc[vc]);

    // It may be helpful to regurgitate the contents of gens.
    if (TraceIsOn("ccgen-debug"))
    {
      Trace("ccgen-debug") << "expansions [";
      bool first_time = true;
      for (const Node& expansion : gens)
      {
        if (!first_time)
        {
          Trace("ccgen-debug") << ", ";
        }

        Trace("ccgen-debug") << expansion;

        first_time = false;
      }
      Trace("ccgen-debug") << "]" << std::endl;

      Trace("ccgen-debug") << "substitution " << subs << std::endl;
    }

    // vc has no neighbors.  We still assume that the length of our walk has
    // increased by one, we elect to expand the element at the next index in fvs
    // (wrapping around), and skip the rest of the loop body.
    if (gens.empty())
    {
      rindex = rindex + 1 == fvs.size() ? 0 : rindex + 1;
      Trace("ccgen-debug") << "...no generalizations" << std::endl;
      // nothing to generalize
      continue;
    }

    // We choose to expand vc to gens[gindex] which we copy over to g.
    size_t gindex = Random::getRandom().pick(0, gens.size() - 1);
    Node g = gens[gindex];

    // Let's give some thought to what we're about to do here.  We have a
    // substitution subs and we want to maintain the invariant that the
    // substitution is idempotent.  Equivalently, we want to guarantee that its
    // domain is disjoint from the set of equivalence class variables that occur
    // in its image.  We intend to grow subs to a new substitution (let's refer
    // to it as subs') by mapping vc to some term gs (don't ask me why Andy
    // named it gs).  We should ensure the following.
    //
    // 1.  if vc is in the domain of subs then subs[vc] and subs'[vc] are the
    // same,
    //
    // 2.  vc does not occur in the image of subs',
    //
    // 3.  none of the equivalence class variables in gs occurs in the domain of
    // subs'.
    //
    // We can argue that condition #1 is already satisfied.  To ensure #3 is
    // satisfied we define gs as subs.apply(g), then we give up whenever vc
    // occurs in gs.  Why does this work?  g's equivalence class variables can
    // be partitioned into those that occur in the domain of subs and those that
    // don't.  Any variable that occurs in the domain of subs will not appear in
    // gs because subs is idempotent.  However, vc will appear in the domain of
    // subs' so we want to ensure that vc does not occur in gs.  Assuming vc
    // does not occur in gs all that's left is to fulfil condition #2.  We can
    // do this by applying the singleton substitution {vc -> gs}, which we'll
    // later store in the variable stmp, to every term in the image of subs as
    // we construct subs'.  Note that subs' is an abstract variable.  In truth
    // subs is destructively modified.
    //
    // We should also think about how to update both cur and fvs.  To update cur
    // we need only apply the singleton substitution {vc -> gs} to it.  I feel
    // that to update fvs it is enough to insert the equivalence class variables
    // of gs after vc's position and erase the element at vc's position.  The
    // business with isDag seems unnecessary.

    // This is the first step to ensuring that gs satisfies property #3.  After
    // this we can be certain that the equivalence class variables that occur in
    // gs don't also occur in the domain of subs.  However vc may still occur in
    // gs.
    Node gs = subs.apply(g);

    // If vc occurs in gs we shy away from expanding vc, we still assume that
    // the length of our walk has increased by 1, once again randomly pick an
    // equivalence class variable that occurs in cur possibly re-grabbing vc,
    // then fast-forward to the next iteration.
    if (expr::hasSubterm(gs, vc))
    {
      Trace("ccgen-debug") << "...cyclic to " << gs << std::endl;
      rindex = Random::getRandom().pick(0, fvs.size() - 1);
      // cyclic, skip
      continue;
    }

    // If we're at this point in the code we know gs satisfies condition #3.  We
    // just need to ensure that subs' satisfies condition #2.

    // stmp is the singleton substitution {vc -> gs}.
    Subs stmp;
    stmp.add(vc, gs);

    // This ensures that neither vc nor any equivalence class variable that
    // occurs in the domain of subs also occurs in the image of subs.
    stmp.applyToRange(subs);

    // We destructively update subs to arrive at subs'.  Since we performed an
    // applyToRange() above we know that the updated subs satisfies condition #2.
    subs.add(vc, gs);

    // Update cur as described above.
    cur = stmp.apply(cur);

    // Also update fvs as described above.  Removing vc is the first step.
    fvs.erase(fvs.begin() + rindex);

    // The second step: all equivalence class variables that occur in `gs` and
    // do not occur in `fvs` must be added to `fvs`.  We gather the variables in
    // `gs_vars` before adding them.  Note that `expr::getVariables()` will grab
    // user-defined function symbols.  We should make sure that we're only
    // adding terms with the kind `BOUND_VARIABLE` to `fvs`.
    std::unordered_set<Node> gs_vars;
    expr::getVariables(gs, gs_vars);

    for (const Node& var : gs_vars)
    {
      if ((var.getKind() == Kind::BOUND_VARIABLE) &&
          (std::find(fvs.begin(), fvs.end(), var) == fvs.end()))
      {
        fvs.insert(fvs.begin() + rindex, var);
      }
    }

    // Trace("ccgen-debug-expand") << "...expand to " << gs << std::endl;
    // std::vector<Node> newVars;
    // if (g.getNumChildren() > 0)
    // {
    //   bool isDag = false;
    //   for (const Node& gv : g)
    //   {
    //     if (subs.contains(gv))
    //     {
    //       // already handled
    //       isDag = true;
    //     }
    //     else if (std::find(fvs.begin(), fvs.end(), gv) == fvs.end())
    //     {
    //       newVars.push_back(gv);
    //     }
    //     else
    //     {
    //       // already in progress of being handled
    //       isDag = true;
    //     }
    //   }
    //   if (isDag)
    //   {
    //     rindex = Random::getRandom().pick(0, fvs.size() - 1);
    //     continue;
    //   }
    // }

    // fvs.erase(fvs.begin() + rindex);
    // for (const Node& gv : newVars)
    // {
    //   auto it = std::lower_bound(fvs.begin(), fvs.end(), gv);
    //   fvs.insert(it, gv);
    // }
    // Trace("ccgen-debug") << "...free variables now " << fvs << std::endl;

    Trace("cconjGen") << "(quote " << cur << ")" << std::endl;

    // cur is now a candidate term.  Recalling the description we had provided
    // earlier: we have reached cur during a random walk that started at v.
    // Therefore we should record cur in grecs.  (Recall also that grecs is a
    // reference to the vector that stores the vertices that we know are
    // reachable from v.)
    grecs.emplace_back(cur);

    // We must also record cur in our index of expansions.
    addGeneralizationTerm(cur, v, i, fvs);

    // If there are no variables to expand we bring our random walk to a halt.
    if (fvs.empty())
    {
      break;
    }

    // We will expand fvs[rindex] in the next iteration of this loop.
    rindex = Random::getRandom().pick(0, fvs.size() - 1);
  }
}

void ConflictConjectureGenerator::addGeneralizationTerm(
    const Node& g, const Node& v, size_t depth, const std::vector<Node>& fvs)
{
  if (d_genToFv.find(g) != d_genToFv.end())
  {
    return;
  }
  Trace("ccgen-terms") << "* Generalization term [" << v << "]: " << g
                       << std::endl;
  Trace("ccgen-debug") << "- free variables are " << fvs << std::endl;
  d_genToFv[g] = fvs;
  GenTrie* gt = &d_gtrie;
  for (const Node& fv : fvs)
  {
    gt = &gt->d_children[fv];
  }
  gt->d_gens.emplace_back(g, v);
}

void ConflictConjectureGenerator::GenTrie::clear()
{
  d_children.clear();
  d_gens.clear();
}

// void ConflictConjectureGenerator::findCompatibleOld(
//     const Node& g,
//     const std::vector<Node>& fvs,
//     const Node& vlhs,
//     GenTrie* gt,
//     ConflictConjectureGenerator::State state,
//     size_t fvindex)
// {
//   if (state != State::SUBSET || fvindex == fvs.size())
//   {
//     for (const std::pair<Node, Node>& cg : gt->d_gens)
//     {
//       if (cg.second == vlhs)
//       {
//         if (state == State::SUBSET)
//         {
//           candidateConjecture(cg.first, g);
//         }
//         else
//         {
//           candidateConjecture(g, cg.first);
//         }
//       }
//       else
//       {
//         Trace("ccgen-debug")
//             << "- found term " << cg.first << " but not for lhs " << vlhs
//             << " vs " << cg.second << std::endl;
//       }
//     }
//   }
//   Trace("ccgen-debug") << "  findCompatible " << fvindex << "/" << fvs.size()
//                        << " state = " << static_cast<int>(state) << std::endl;
//   Assert(state != State::UNKNOWN || fvindex < fvs.size());
//   for (std::pair<const Node, GenTrie>& cg : gt->d_children)
//   {
//     if (fvindex < fvs.size() && cg.first == fvs[fvindex])
//     {
//       Assert(state != State::SUPERSET);
//       State newState = fvindex + 1 == fvs.size() ? State::SUBSET : state;
//       findCompatible(g, fvs, vlhs, &cg.second, newState, fvindex + 1);
//     }
//     else if (std::find(fvs.begin() + fvindex, fvs.end(), cg.first) != fvs.end())
//     {
//       // we skipped a variable
//       if (state != State::SUBSET)
//       {
//         findCompatible(g, fvs, vlhs, &cg.second, State::SUPERSET, fvindex);
//       }
//     }
//     else if (state != State::SUPERSET)
//     {
//       findCompatible(g, fvs, vlhs, &cg.second, State::SUBSET, fvindex);
//     }
//   }
// }

void ConflictConjectureGenerator::findCompatible(
    const Node& tgt_exp,
    const std::vector<Node>& tgt_vars,
    const Node& rt_var,
    const GenTrie* cur,
    const std::vector<Node> cur_vars,
    const size_t n_inter,
    const ConflictConjectureGenerator::State st)
{
  // *Variable names*
  //
  // 'tgt_exp' --> 'target expansion', 'tgt_vars' --> 'target
  // variables', 'rt_var' --> 'root variable', 'cur' --> 'cursor',
  // 'cur_vars' --> 'variables in path to cursor', 'n_inter' -->
  // 'number of elements in intersection', 'st' --> 'state'.

  // *Expectations*
  //
  // Expects that `tgt_vars` is a vector of equivalence class
  // variables, and that it does not have duplicate elements.
  // Consequently `tgt_vars` can be treated as a set.
  //
  // Expects that the set of equivalence class variables that occur in
  // `tgt_exp` is exactly `tgt_vars`.
  //
  // Expects that `rt_var` is an equivalence class variable.
  //
  // This function expects that in any top-level call to
  // `findCompatible()` (1) `cur` is `&d_gtrie`, (2) `cur_vars` is an
  // empty vector, (3) `n_inter` is 0, and (4) `st` is `SUBSET`.

  // *Invariants*
  //
  // `tgt_exp`, `tgt_vars` and `rt_var` never change in recursive calls.
  //
  // `cur_vars` is a vector of equivalence class variables, it does
  // not have duplicate elements, and it is the path to `*cur` in
  // `d_gtrie`.  It is worth explaining the third part of this
  // invariant in more detail.  Since it's a vector, `cur_vars` has
  // the form {`v_1`, ..., `v_n`}.  It should be that `cur` points to
  // `d_gtrie.d_children[v_1](...).d_children[v_n]`.  As a consequence
  // of this property and the properties of `d_gtrie`, we can make the
  // stronger claim that for every pair (`exp`, `var`) in
  // `cur->d_gens`, `exp` is an expansion whose root equivalence class
  // variable is `var` and the set of equivalence class variables that
  // occur in `exp` is exactly `cur_vars`.
  //
  // `t_inter` is the size of the intersection of (the sets of
  // elements in) `tgt_vars` and `cur_vars`.  Therefore if `t_inter`
  // equals `tgt_vars.size()` then `cur_vars` must be a superset of
  // `tgt_vars`.  Similarly if `t_inter` equals `cur_vars.size()` then
  // `cur_vars` must be a subset of `tgt_vars`.
  //
  // `st` is one of `SUBSET` or `SUPERSET`.  Never `UNKNOWN`.  `st` is
  // `SUPERSET` if and only if `cur_vars` has at least one element
  // that is absent from `tgt_vars`.  It *does not* mean that
  // `cur_vars` is truly a superset of `tgt_vars`.  Instead it
  // indicates our intent to grow `cur_vars` till it is truly a
  // superset of `tgt_vars` i.e. when `t_inter` equals
  // `tgt_vars.size()`.  The previous sentences about `st` together
  // imply that `st` is `SUBSET` if and only if all elements of
  // `cur_vars` are also in `tgt_vars`.  In this case `cur_vars` is
  // actually a subset of `tgt_vars`.

  // *Objective*
  //
  // This function's objective is to find as many expansions `exp` as
  // possible, derived from the equivalence class variable `rt_var`,
  // such that `exp` is *compatible* with the target expansion
  // `tgt_exp`.  `exp` is considered to be compatible with `tgt_exp`
  // when the set of equivalence class variables that occur in one is
  // a subset of the equivalence class variables that occur in the
  // other.  In other words either `cur_vars` is a subset of
  // `tgt_vars`, or `tgt_vars` is a subset of `cur_vars`.  Once an
  // `exp` that meets the above conditions is found, it is paired with
  // `tgt_exp` and promoted to a candidate conjecture.

  // *Strategy*
  //
  // We will start each call to `findCompatible()` by checking whether
  // `cur_vars` is a subset of `tgt_vars` or vice versa.  If so, we
  // will rifle through the expansion-variable pairs (`exp`, `var`) at
  // `*cur`.  For each pair where `var` is equal to `rt_var`, we can
  // be sure that `exp` is an expansion derived from `rt_var` that is
  // compatible with `tgt_exp`.  With this surety we can call
  // `candidateConjecture()` to indicate that one, not both, of `exp =
  // tgt_exp` or `tgt_exp = exp` should be considered a candidate
  // conjecture.  To meet the expectation of `candidateConjecture()`
  // we ensure that the equivalence class variables that occur in its
  // first argument make a superset of the equivalence class variables
  // in its second argument.  To say it another way if `cur_vars` is a
  // subset of `tgt_vars` we will call `candidateConjecture(tgt_exp,
  // exp)` otherwise we'll flip the order of arguments.
  //
  // Next, we elect to make one recursive call to `findCompatible()`
  // for each child of `*cur`.  Recall that the children of `*cur` are
  // essentially instances `trie` of `GenTrie` each labeled with a
  // unique equivalence class variable `lbl` (lbl is short for label).
  // For each trie-label pair we call `findCompatible()` with updated
  // values for the variables that are changeable.  `tgt_exp`,
  // `tgt_vars` and `rt_var` are not changeable.  `cur` is updated to
  // `&trie` while `cur_vars` is updated to include the variable
  // `lbl`.  If `lbl` occurs in `tgt_vars` then `n_inter` is bumped by
  // 1 and `st` is left as-is.  On the other hand if `lbl` does not
  // occur in `tgt_vars` then `n_inter` is left as-is, while `st` is
  // updated to `SUPERSET`.  Note that the use of 'updated' in the
  // previous sentences does not imply that `cur_vars` is
  // destructively modified.  Instead, as the qualifiers on this
  // function's arguments suggest, we make a fresh vector to pass
  // along to each recursive call.
  //
  // **TODO**.  At the moment we perform an exhaustive search over the
  // trie with no restrictions on the choice of `lbl`.  It might be
  // more pragmatic to have a heuristic that maintains a bound on the
  // size of the difference between `cur_vars` and `tgt_vars`.  Let's
  // say we wanted to bound the size of the difference to at most 2
  // variables.  Then if `st == SUPERSET` and `tgt_vars` has at least
  // 2 variables that are not in `cur_vars` then we will restrict our
  // choices of `lbl` to equivalence class variables that occur in
  // `tgt_vars`.  If `st == SUBSET` we will not restrict our choices
  // of `lbl`.  Also, even if one of `cur_vars` and `tgt_vars` is a
  // subset of the other, we will only make candidate conjectures when
  // the difference between their sizes is less or equal to 2.

  // First discover compatible expansions.

  // cur_sub_tgt --> is `cur_vars` a subset of `tgt_vars`?
  const bool cur_sub_tgt = (n_inter == cur_vars.size());

  // tgt_sub_cur --> is `tgt_vars` a subset of `cur_vars`?
  const bool tgt_sub_cur = (n_inter == tgt_vars.size());

  if (cur_sub_tgt || tgt_sub_cur)
  {
    for (const std::pair<Node, Node>& entry : cur->d_gens)
    {
      // exp --> expansion.  `exp` is compatible with `tgt_exp`.  Set
      // of equivalence class variables in `exp` is exactly
      // `cur_vars`.
      const Node& exp = std::get<0>(entry);

      // var --> variable.  `exp` is an expansion derived from the
      // equivalence class variable `var`.
      const Node& var = std::get<1>(entry);

      if (var == rt_var)
      {
        Trace("cconjGen") << "(quote " << exp << ")" << std::endl;

        // Remember that `candidateConjecture()` expects the
        // equivalence class variables that occur in its first
        // argument to be a superset of the equivalence class
        // variables that occur in its second argument.

        if (cur_sub_tgt)
        {
          candidateConjecture(tgt_exp, exp);
        }
        else
        {
          // `tgt_sub_cur` must be true.
          candidateConjecture(exp, tgt_exp);
        }
      }
    }
  }

  // Then make recursive calls.

  for (const std::pair<Node, GenTrie> entry : cur->d_children)
  {
    const Node& lbl = std::get<0>(entry);
    const GenTrie& trie = std::get<1>(entry);

    // Will pass `next_vars` in the position of `cur_vars` in each recursive call.
    std::vector<Node> next_vars{};
    next_vars.insert(next_vars.end(), cur_vars.begin(), cur_vars.end());
    next_vars.push_back(lbl);

    if (std::find(tgt_vars.begin(), tgt_vars.end(), lbl) != tgt_vars.end())
    {
      // `lbl` is in `tgt_vars`.
      findCompatible(tgt_exp, tgt_vars, rt_var, &trie, next_vars, n_inter + 1, st);
    }
    else
    {
      // `lbl` is not in `tgt_vars`.
      findCompatible(tgt_exp, tgt_vars, rt_var, &trie, next_vars, n_inter, State::SUPERSET);
    }
  }
}

/**
 * The state of finding E-matches for a term in an equalivalence class
 */
class EMatchFrame
{
 public:
  EMatchFrame() {}
  /**
   * Initialize the list of terms in the equivalance class of r that may match
   * m.
   */
  EMatchFrame(TermDb* tdb, eq::EqualityEngine* ee, const Node& m, const Node& r)
      : d_toMatch(m), d_index(0)
  {
    Assert(ee->hasTerm(r) && ee->getRepresentative(r) == r && r.isConst());
    Node op = m.getOperator();
    // maps argument positions to the ground term representative of that
    // argument, for the ground arguments of m.
    std::map<size_t, Node> groundArgs;
    for (size_t i = 0, nargs = m.getNumChildren(); i < nargs; i++)
    {
      if (m[i].getKind() == Kind::BOUND_VARIABLE)
      {
        d_varArgs.push_back(i);
      }
      else if (!expr::hasBoundVar(m[i]))
      {
        Assert(ee->hasTerm(m[i]));
        groundArgs[i] = ee->getRepresentative(m[i]);
      }
      else
      {
        d_recArgs.push_back(i);
      }
    }
    // get the candidate terms in this equivalence class
    eq::EqClassIterator eqc = eq::EqClassIterator(r, ee);
    while (!eqc.isFinished())
    {
      Node n = *eqc;
      ++eqc;
      // must have the same operator, and be "active". The latter restriction
      // will filter terms that are congruent to another term we already
      // considered.
      if (!n.hasOperator() || n.getOperator() != m.getOperator()
          || !tdb->isTermActive(n))
      {
        continue;
      }
      Assert(n.getNumChildren() == m.getNumChildren());
      // prune ground disequal
      bool success = true;
      for (std::pair<const size_t, Node>& g : groundArgs)
      {
        Assert(g.first < n.getNumChildren());
        Assert(ee->hasTerm(n[g.first]));
        Node gr = ee->getRepresentative(n[g.first]);
        if (gr != g.second)
        {
          success = false;
          break;
        }
      }
      if (success)
      {
        d_matches.push_back(n);
      }
    }
  }
  /** The term we are matching */
  Node d_toMatch;
  /** The candidate list of terms */
  std::vector<Node> d_matches;
  /** The next index in d_matches to consider */
  size_t d_index;
  /** The argument positions of d_toMatch which are non-ground, non-variable */
  std::vector<size_t> d_recArgs;
  /** The argument positions of d_toMatch which are variables */
  std::vector<size_t> d_varArgs;
  /**
   * The set of variables we bound in the last successful call to push, if any.
   */
  std::unordered_set<size_t> d_varArgsBound;
  /**
   * Update match/emf based on matching the next term in the list of candidate
   * terms computed in the constructor of this class. This adds
   * - substitutions to match based on binding the direct variables of d_toMatch
   * - a list of obligations to match recursively to emf based on the
   * non-ground, non-variable chidlren of d_toMatch.
   *
   * @return true if we successfully pushed to match/emf.
   */
  bool push(TermDb* tdb,
            eq::EqualityEngine* ee,
            Subs& match,
            std::vector<std::shared_ptr<EMatchFrame>>& emf)
  {
    Trace("cconj-em-debug") << "push " << std::endl;
    if (isFinished())
    {
      Trace("cconj-em-debug") << "...already finished" << std::endl;
      return false;
    }
    Node nextMatch = d_matches[d_index];
    d_index++;
    Assert(nextMatch.getNumChildren() == d_toMatch.getNumChildren());
    std::vector<Node> groundRec;
    for (size_t i : d_recArgs)
    {
      Assert(i < nextMatch.getNumChildren());
      Assert(ee->hasTerm(nextMatch[i]));
      Node r = ee->getRepresentative(nextMatch[i]);
      if (!r.isConst())
      {
        // non-constant
        Trace("cconj-em-debug") << "...non-const" << std::endl;
        return false;
      }
      groundRec.emplace_back(r);
    }
    Trace("cconj-em-debug") << "look at var args" << std::endl;
    // match the current vars
    for (size_t i : d_varArgs)
    {
      const Node& v = d_toMatch[i];
      Assert(v.getKind() == Kind::BOUND_VARIABLE);
      Node cur = match.getSubs(v);
      if (cur.isNull())
      {
        d_varArgsBound.insert(i);
        match.add(v, nextMatch[i]);
        continue;
      }
      Assert(ee->hasTerm(nextMatch[i]));
      if (!ee->areEqual(nextMatch[i], cur))
      {
        // failed a bound argument argument
        pop(match);
        Trace("cconj-em-debug") << "...bound conflict" << std::endl;
        return false;
      }
    }
    Trace("cconj-em-debug") << "push" << std::endl;
    Assert(groundRec.size() == d_recArgs.size());
    for (size_t i = 0, ngr = groundRec.size(); i < ngr; i++)
    {
      emf.emplace_back(std::make_shared<EMatchFrame>(
          tdb, ee, d_toMatch[d_recArgs[i]], groundRec[i]));
    }
    Trace("cconj-em-debug") << "...return success" << std::endl;
    return true;
  }
  /**
   * Pop, which cleans up match based on what was bound by this class in the
   * last successful call to push.
   */
  void pop(Subs& match)
  {
    for (size_t i : d_varArgsBound)
    {
      match.erase(d_toMatch[i]);
    }
    d_varArgsBound.clear();
  }
  bool isFinished() const { return d_index == d_matches.size(); }
};

void ConflictConjectureGenerator::candidateConjecture(const Node& lhs_cand,
                                                      const Node& rhs_cand)
{
  // *Argument names*
  //
  // lhs_cand --> 'left hand side of candidate equality conjecture',
  // rhs_cand --> 'right hand side of candidate equality conjecture'.

  // *Expectations*
  //
  // This function expects that the set of equivalence class variables
  // occurring in `lhs_cand` is a superset of the equivalence class
  // variables occuring in `rhs_cand`.

  // If `lhs_cand` and `rhs_cand` are identical then the candidate
  // conjecture will be trivially valid, not to mention useless.  We
  // are instead looking for a candidate that is not deductively
  // entailed in the current model and instead warrants a proof by
  // induction.
  if (lhs_cand == rhs_cand)
  {
    return;
  }

  if (lhs_cand.getKind() == Kind::BOUND_VARIABLE)
  {
    // If we're here, it means that `lhs_cand` is an equivalence class
    // variable.  Consequently we know that the equivalence class
    // variables occurring in `rhs_cand` are a subset of the singleton
    // set { `lhs_cand` }.  We expect `rhs_cand` to have at least 1
    // equivalence class variable, so the set of equivalence class
    // variables occurring in `rhs_cand` must be exactly { `lhs_cand`
    // }.  We also know that `rhs_cand` isn't itself an equivalence
    // class variable, because otherwise the condition `lhs_cand ==
    // rhs_cand` would have been satisfied.  It follows that
    // `rhs_cand` must be an application of some operator,
    // specifically a constructor or an uninterpreted function.


    if (expr::hasSubterm(rhs_cand, lhs_cand))
    {
      // corner case of the form x = t[x], flip sides
      candidateConjecture(rhs_cand, lhs_cand);
    }
    // otherwise, definitely bogus
    return;
  }

  Node a = lhs_cand;
  Node b = rhs_cand;
  if (a.getKind() == Kind::APPLY_CONSTRUCTOR
      && b.getKind() == Kind::APPLY_CONSTRUCTOR)
  {
    if (a.getOperator() != b.getOperator())
    {
      // obviously clashing
      return;
    }
    Assert(a.getNumChildren() == b.getNumChildren());
    Node eq;
    // if constructor equals constructor, traverse to single argument that is
    // different
    for (size_t i = 0, nargs = a.getNumChildren(); i < nargs; i++)
    {
      if (a[i] != b[i])
      {
        if (eq.isNull())
        {
          eq = a[i].eqNode(b[i]);
          continue;
        }
        return;
      }
    }
    Assert(!eq.isNull());
    // TODO: check free variable property
    candidateConjecture(eq[0], eq[1]);
    return;
  }
  Node lem = a.eqNode(b);
  d_conjBuffer.insert(lem);
}

bool ConflictConjectureGenerator::filterConjecture(Node clem)
{
  // We must ignore this conjecture if the generator has been switched off.
  if (d_switched_off)
  {
    return true;
  }

  Trace("cconj-gen") << "filterConjecture(" << clem << ")" << std::endl;

  Trace("cconjGen") << "(list \"filter\" (quote " << clem << ")";

  Trace("cconj-filter") << "Candidate conjecture : " << clem[0]
                        << " == " << clem[1] << "?" << std::endl;
  if (d_conjGenCache.find(clem) != d_conjGenCache.end())
  {
    Trace("cconj-filter") << "...already in cache" << std::endl;
    Trace("cconjGen") << " (list \"cache\" #f))" << std::endl;
    return true;
  }
  else
  {
    Trace("cconjGen") << " (list \"cache\" #t)";
  }
  Node a = clem[0];
  Node b = clem[1];

  // if (options().quantifiers.ccgenFilterEval)
  // {
  //   Trace("cconj-filter") << "Try filter based on evaluation" << std::endl;
  //   if (filterEvalsToFalse(a, b))
  //   {
  //     Trace("cconj-filter") << "...filtered based on evaluation" << std::endl;
  //     Trace("cconjGen") << " (list \"evaluation\" #f))" << std::endl;
  //     return true;
  //   }
  //   else
  //   {
  //     Trace("cconjGen") << " (list \"evaluation\" #t)";
  //   }
  // }

  int tested = 0;

  if (d_banned.find(clem) != d_banned.end())
  {
    Trace("cconj-filter") << "Filtered based on banlist." << std::endl;
    return true;
  }

  const bool discard = filterEmatching(a, b, tested);
  Trace("cconj-filter") << "Try filter based on E-matching" << std::endl;
  if (discard)
  {
    Trace("cconj-filter") << "...filtered based on E-matching" << std::endl;
    Trace("cconjGen") << " (list \"e-matching\" #f))" << std::endl;

    // If clem has a counterexample we should never consider it.
    d_banned.insert(clem);

    return true;
  }
  else
  {
    Trace("cconjGen") << " (list \"e-matching\" #t)";
  }

  Trace("cconj-filter") << "Try filter based on deductively entailed"
                        << std::endl;
  if (filterDeductivelyEntailed(a, b))
  {
    Trace("cconj-filter") << "...filtered based on deductively entailed"
                          << std::endl;
    Trace("cconjGen") << " (list \"entailment\" #f))" << std::endl;

    // If clem is deductively entailed now, it will be deductively entailed
    // later as well.  Let's ban it.
    d_banned.insert(clem);

    return true;
  }
  else
  {
    Trace("cconjGen") << " (list \"entailment\" #t)";
  }

  Trace("cconj-filter") << "Try filter based on inductively entailed"
                        << std::endl;
  // If clem is inductively entailed we want to keep it around!  If it
  // is not inductively entailed then we reject it.
  if (filterInductivelyEntailed(clem))
  {
    NodeManager* node_mgr = nodeManager();
    std::unordered_set<Node> fvs_set{};
    expr::getFreeVariables(clem, fvs_set);
    std::vector<Node> fvs{};
    fvs.insert(fvs.end(), fvs_set.begin(), fvs_set.end());
    const Node bvs = node_mgr->mkNode(Kind::BOUND_VAR_LIST, fvs);
    Node lem = node_mgr->mkNode(Kind::FORALL, bvs, clem);
    Trace("cconj-filter") << "...inductively entailed, asserting " << lem << " immediately...";
    bool result = d_qim.addPendingLemma(lem, InferenceId::QUANTIFIERS_CONFLICT_CONJ_GEN_SPLIT);
    Trace("cconj-filter") << "...tried with result " << result << std::endl;

    Trace("cconj-filter2") << "ASSUMED " << clem << std::endl;
  }
  else
  {
    Trace("cconj-filter") << "...rejected since not inductively entailed"
                          << std::endl;

    Trace("cconj-filter2") << "PROMISING " << clem << std::endl;

    return true;
  }

  // if (filterManual(clem, tested))
  // {
  //   return true;
  // }

  Trace("cconjGen") << ")" << std::endl;

  // Reject unconditionally for now, since if inductively entailed we
  // assert it immediately.  If we don't reject it here it might get
  // added as a splitting lemma which would be inefficient.
  return true;
}

/**
 * Both `lhs` and `rhs` are expansions.  (Recall that all expansions are built
 * from user-declared function symbols, constructor symbols, and equivalence
 * class variables.)  We assume that `lhs` is the left-hand side of a candidate
 * equality conjecture while `rhs` is its right-hand side.  We also assume that
 * every equivalence class variable that occurs in `rhs` also occurs in `lhs`.
 * Let 'X' be the set of equivalence class variables that occur in `lhs`.  We
 * want to check whether the following conjecture evaluates to false on some
 * substitution of terms from the term database.
 *
 * forall X. lhs = rhs
 *
 * Since `lhs` contains equivalence class variables it can be treated as a
 * pattern for e-matching.  For each equivalence class representative `rep`, we
 * scan `rep`'s equivalence class for terms `t` that match the pattern `lhs`.
 * In other words we search for substitutions `subs` over X such that (`lhs` *
 * `subs`) is equivalent to `rep`.  (Since X subsumes the equivalence class
 * variables of `rhs` we can be sure that (`rhs` * `subs`) is also a ground
 * term.)  Then we check whether (`lhs` * `subs`) and (`rhs` * `subs`) are in
 * the same equivalence class.  If there is at least one substitution for which
 * they are in different equivalence classes, we return true to signal that the
 * candidate conjecture should be discarded.  We want to test with as many
 * substitutions as we can.
 *
 * I've added on a new argument `out_tested`, short for 'output tested'.  This
 * function has a local variable named `tested` that counts how many
 * substitutions we've tested the conjecture with.  Just before returning from
 * this function we test `out_tested` to the value of `tested` so that we can
 * share it with the caller.
 */
bool ConflictConjectureGenerator::filterEmatching(Node lhs, Node rhs, int& out_tested)
{
  // We assume that `lhs` has an operator.  Clearly this assumption
  // would make us reject the following reasonable conjectures.
  //
  // - forall n. n == plus(n, zero())
  // - forall n. n == times(n, succ(zero()))
  //
  // These are perfectly good conjectures if we assume plus and times
  // are defined the usual way on the natural numbers.  So in addition
  // to making sure that the variables of `lhs` subsume the variables
  // of `rhs`, let's also make sure that `lhs` has an operator.
  if (!lhs.hasOperator())
  {
    return false;
  }
  const Node& op = lhs.getOperator();

  // We'll need to pass a pointer to the current term database when we
  // call the member functions of `Decision`.
  TermDb* term_db = getTermDatabase();

  // A pointer to the current entailment checker will help us check
  // whether `lhs` and `rhs` are entailed to be equal under the
  // substitutions we'll discover.
  EntailmentCheck* ent_chk = d_treg.getEntailmentCheck();

  // `good_reps` will store the 'good' equivalence class
  // representatives.  These are representatives that are 'constant'
  // in the sense of `isConst()` and also have the same sort as `lhs`.
  std::vector<Node> good_reps;

  // Populate `good_reps` in the loop below.

  // 'rep_it' is short for 'iterator over representatives'.
  eq::EqClassesIterator rep_it = eq::EqClassesIterator(d_ee);
  while (!rep_it.isFinished())
  {
    // 'rep' is short for 'representative'.
    const Node& rep = *rep_it;

    ++rep_it;

    if (rep.isConst() && rep.getType() == lhs.getType())
    {
      good_reps.push_back(rep);
    }
  }

  // We will use tested to count the number of substitutions 'subs'
  // found so far such that (`lhs` * subs) and (`rhs` * subs) are
  // ground.
  size_t tested = 0;

  // We will use tested to count the number of substitutions 'subs'
  // found so far such that (`lhs` * subs) and (`rhs` * subs) are
  // ground and are also in the same equivalence class.  It should be
  // clear that `confirmed` <= `tested`.
  size_t confirmed = 0;

  for (const Node& rep : good_reps)
  {
    // Start with the empty substitution.
    Subs subs;

    // Create the queue of decision points, `trail`, where each
    // decision point is represented by an instance of the `Decision`
    // class.  This queue is slightly strange because it is
    // implemented by combining a vector, `decs`, with an index,
    // `lvl`, that tracks the front element of the queue.  Elements
    // are added to the queue by pushing them on to the end of the
    // vector.  Elements can be 'removed' in two ways.  They can be
    // popped from the vector, which corresponds to removing elements
    // from the end of the queue.  Furthermore the index of the
    // element at the front of the queue can be incremented, which
    // corresponds to dequeuing elements in the expected FIFO fashion.
    // Any element dequeued in the latter manner can be restored by
    // decrementing the same index.
    Trail decs{};

    // Add the first decision point to the queue.
    // init_dec --> 'initial decision'.
    Trace("ConflictConjectureGenerator::filterEmatching") << "Calling Decision() >>>>>" << std::endl;
    decs.emplace_back(new Decision(term_db, d_ee, lhs, rep, 0, false));
    Trace("ConflictConjectureGenerator::filterEmatching") << "<<<<< Returned from call to Decision()" << std::endl;

    // `lvl`, short for 'decision level', is the index that represents
    // the front of the queue whose elements are stored in `decs`.
    // We'll bump it as we proceed and decrement it when we need to
    // backtrack.
    size_t lvl = 0;

    // Before we look at the code for the loop let's make sure that we
    // clearly state our two invariants.
    //
    // 1.  `decs.size()` >= `lvl` >= 0.
    //
    // 2.  We work to maintain the invariant that at the beginning of
    // an iteration if `lvl` >= 0 then `decs[lvl]` has *effectively*
    // not contributed to the current substitution.  In other words if
    // `decs[lvl].push()` had been called in the past, then any
    // mappings it added to the substitution have since been removed
    // with `decs[lvl].pop()`.  As a consequence, if `lvl` > 0 then
    // the most recent call to `push()` was effectively `decs[lvl -
    // 1].push()`.

    // Let's also be clear that we leave the loop when backtracking is
    // impossible, which happens when `decs.size()` is 0.  Even if the
    // queue is considered 'empty' due to `lvl` = `decs.size()` we
    // still try to backtrack by decrementing `lvl`.  This is because
    // we want to find as many grounding substitutions as possible,
    // instead of just one.

    // We will set this to `false` when it's time to leave the loop.
    bool go_on = true;
    while (go_on)
    {
      // Our actions in each iteration of the loop are governed by the
      // answers to three questions.  Is the front index `lvl` within
      // the bounds of the vector `decs`?  If it is, are there still
      // terms to explore in the e-matching job at that index?  If
      // there are, can we execute the e-matching job at the index
      // successfully?  This suggests that there are four distinct
      // situations to handle.  They are labeled 'Situation 1' through
      // 'Situation 4' in the code below.

      // Note.  The index into `decs` that denotes the back element of
      // the decision queue is (`decs.size()` - 1).  When `lvl`
      // exceeds `max_lvl` we can claim that there are no more
      // decisions to be made.  This means that we have found a
      // substitution and also that once we test this substitution we
      // should backtrack so that we can find more substitutions.
      const size_t max_lvl = decs.size() - 1;

      if (lvl > max_lvl)
      {
        // Situation 1.  `lvl` is not a valid index into `decs`.
        // There are no pending decisions.  This means we have found a
        // substitution `subs` such that `lhs` under `subs` is in a
        // known equivalence class.

        // We should print the substitution.
        // std::cout << "Found grounding substitution: " << subs << std::endl;

        // We need to check whether the LHS and RHS are equivalent
        // under the substitution.

        // rhs_img --> image of RHS under subs.
        const Node rhs_img = subs.apply(rhs);

        // We have a guarantee that the image of `lhs` under `subs` is
        // in the known equivalence class of `rep` because we used it
        // to compute the substitution `subs`.  We have no such
        // guarantee for `rhs_img`.  However we can check this by
        // getting the 'entailed term' for `rhs_img` and making sure
        // it's not `Node::null()`.  rhs_img_ent --> entailed term for
        // image of RHS.
        const Node rhs_img_ent = ent_chk->getEntailedTerm(rhs_img);

        if (!rhs_img_ent.isNull())
        {
          Trace("filterEmatching") << "before call to getRepresentative() in filterEmatching()" << std::endl;
          // rhs_img_rep --> representative of equivalence class of
          // `rhs_img_ent`.
          const Node rhs_img_rep = d_ee->getRepresentative(rhs_img_ent);
          Trace("filterEmatching") << "after call to getRepresentative() in filterEmatching()" << std::endl;

          if (d_ee->areDisequal(rep, rhs_img_rep, false))
          {
            // The candidate conjecture is unlikely to be valid and
            // should be rejected.
            return true;
          }
          else
          {
            // Yes, it's a bit strange, but we're incrementing
            // `confirmed` before we increment `tested`.
            confirmed++;
          }

          tested++;
        }

        // We need to backtrack so that we can find more grounding
        // substitutions.
        if (lvl > 0)
        {
          --lvl;
          decs[lvl]->pop(subs);
        }
        else
        {
          // `lvl` is 0 so backtracking is impossible.
          go_on = false;
        }
      }
      else
      {
        // dec --> 'decision'.
        Decision* dec = decs[lvl];

        if (dec->isFinished())
        {
          // Situation 2.  `lvl` is a valid index into `decs` but
          // `dec` has no more candidate terms.

          // We need to backtrack.
          if (lvl > 0)
          {
            // The subsequent decisions in `decs`, the ones at index
            // (`lvl` + 1) and up, were pushed with the expectation
            // that `decs[lvl]` would succeed.  Since `decs[lvl]`
            // can't possibly succeed (which is why we're
            // backtracking), all subsequent decisions, i.e. those at
            // index `lvl` and up, need to be removed.
            size_t n_remove = decs.size() - lvl;
            for (size_t i = 0; i < n_remove; i++)
            {
              // dec_del --> 'decision to delete'
              Decision* dec_del = decs.back();
              decs.pop_back();
              delete dec_del;
            }

            // Thanks to our invariant we have that the last `push()`
            // that was performed was effectively `decs[lvl -
            // 1].push()`, and that's what we need to undo with `pop()`.
            decs[lvl - 1]->pop(subs);

            // At the moment `lvl` is not a legal index into `decs`.
            // We set it to the maximum legal index, which is (`lvl` -
            // 1).  We can achieve this with a decrement.
            --lvl;
          }
          else
          {
            go_on = false;
          }
        }
        else if (dec->push(term_db, d_ee, subs, decs))
        {
          // Situation 3.  In this case we simply increment `lvl` and
          // proceed to the next iteration.
          ++lvl;
        }
        else
        {
          // Situation 4.  `lvl` is a valid index into `decs`, `decs[lvl]` is
          // not finished, but `decs[lvl].push()` is unsuccessful.  Even an
          // unsuccessful `push()` can destructively modify `subs` so we run
          // `decs[lvl].pop()` to restore the invariant.

          dec->pop(subs);
        }
      }
    }
  }

  // We didn't find any substitutions on which to evaluate the conjecture.
  if (tested == 0)
  {
    return true;
  }

  Trace("ccgen-filterEmatching") << "Tested " << tested << " substitutions, " << confirmed << " confirmed" << std::endl;

  out_tested = tested;

  return false;
}

bool ConflictConjectureGenerator::filterEmatchingOld(const Node& a, const Node& b)
{
  // Both a and b are expansions.  (Recall that all expansions are
  // built from user-declared function symbols, constructor symbols,
  // and equivalence class variables.)  We assume that a is the
  // left-hand side of a candidate equality conjecture while b is its
  // right-hand side.  We also assume that every equivalence class
  // variable that occurs in b also occurs in a, and that X is the set
  // of equivalence class variables that occur in a.  We want to check
  // whether the following conjecture evaluates to false on some
  // subset of terms from the term database.
  //
  // forall X. a = b
  //
  // Since a contains equivalence class variables it can be treated as
  // a pattern for e-matching.  For each equivalence class
  // representative r, we scan r's equivalence class for terms t that
  // match the pattern a.  In other words we search for substitutions
  // T over X such that a*T is equivalent to r.  (Since X subsumes the
  // equivalence class variables of b we can be sure that b*T is also
  // a ground term.)  Then we check whether a*T and b*T are in the
  // same equivalence class.  If there is at least one T for which a*T
  // and b*T are not equivalent we return true to signal that the
  // aforementioned conjecture should be discarded.

  // Is this check unnecessarily aggressive?  Consider these
  // 'identity' conjectures.
  //
  // - forall n. n == plus(n, zero())
  // - forall n. n == times(n, succ(zero()))
  //
  // These are perfectly good conjectures if we assume plus and times
  // are defined the usual way on the natural numbers.  However this
  // check will cause them to be discarded right away.  **I should
  // probably remove it.**
  if (!a.hasOperator())
  {
    // We don't expect this to happen, but in case it does we given an
    // assertion failure.
    Assert(false);
    return false;
  }

  // TODO: cache E-matching for a, for checking a = b1 and a = b2

  Node op = a.getOperator();
  TermDb* tdb = getTermDatabase();
  EntailmentCheck* ec = d_treg.getEntailmentCheck();

  // We'll collect the equivalence class representatives of the same
  // type as 'a' in this vector.
  std::vector<Node> reps;

  // The loop below populates reps.
  eq::EqClassesIterator eqcs = eq::EqClassesIterator(d_ee);
  while (!eqcs.isFinished())
  {
    Node r = (*eqcs);
    ++eqcs;
    if (r.isConst() && r.getType() == a.getType())
    {
      reps.push_back(r);
    }
  }

  // We will use tested to count the number of substitutions T found
  // so far such that a*T and b*T are ground.
  size_t tested = 0;

  // We will use confirmed to count the number of substitutions T
  // found so far such that a*T and b*T are ground and are also in the
  // same equivalence class.  It should be clear that confirmed <=
  // tested.
  size_t confirmed = 0;

  // We iterate through all the equivalence class representatives that
  // share a's type.
  for (const Node& r : reps)
  {
    Trace("cconj-filter-debug") << "- look in " << r << std::endl;

    // match is the substitution that we build as we perform
    // e-matching.  When we match an equivalence class variable with a
    // ground term we add a new mapping to match.  When we must
    // backtrack we remove a mapping from match.
    Subs match;

    // Note that our objective is to search the equivalence class of r
    // for a term that matches the pattern 'a' yielding a substitution
    // T such that a*T and b*T are not in the same equivalence class.
    // We perform backtracking search to find such a substitution.
    // Now it is clear that if 'a' is a variable or if it is
    // variable-free then no backtracking is necessary.  However if
    // 'a' is an operator application that contains a variable as a
    // proper subterm then we need to search through all the terms in
    // the equivalence class of r.  Furthermore suppose 'a' has the
    // form f(a_1, ..., a_n) and r contains the term f(t_1, ..., t_n).
    // To check whether the latter term matches the former pattern we
    // need to perform n-many additional searches (one for each
    // child).  Given that this function, filterEmatching(), performs
    // 'nested' backtracking searches it stores its continuations as a
    // stack of EMatchFrame instances.  An EMatchFrame instance stores
    // the pattern we want to match against, a vector of terms in a
    // particular equivalence class that might match the pattern, and
    // our position within this vector.
    std::vector<std::shared_ptr<EMatchFrame>> emf;

    // emf[eindex - 1] stores the next e-matching 'job'.  The job is
    // 'run' by calling emf[eindex - 1]->push().  If it succeeds,
    // e-matching jobs for each child are pushed on to emf and eindex
    // is bumped up by 1.  Even if no child jobs were pushed emf is
    // still bumped.  So if (eindex - 1) is equal to emf.size() we
    // know that a grounding substitution for 'a' has been found.
    // However if the job fails then we're forced to backtrack.  We
    // decrement eindex by 1 and remove any 'future' jobs from emf by
    // resizing it to the updated value of eindex.
    size_t eindex = 1;

    // Our first job is of course to find a term from the equivalence
    // class of representative r that matches the pattern 'a'.
    emf.emplace_back(std::make_shared<EMatchFrame>(tdb, d_ee, a, r));

    // We iterate through this loop so long as the job stack is
    // non-empty.
    do
    {
      Assert(0 < eindex);

      Trace("cconj-filter-debug")
          << "match at " << eindex << ", " << emf.size() << std::endl;

      Assert(eindex <= emf.size() + 1);

      if (eindex == emf.size() + 1)
      {
        Trace("cconj-filter-debug")
            << "Matches " << match.toString() << std::endl;
        // should have a complete match, process the right hand side
        Node bs = match.apply(b);
        Node bse = ec->getEntailedTerm(bs);
        Trace("cconj-filter-debug")
            << "...left hand side entailed " << bse << std::endl;
        if (!bse.isNull())
        {
          Node rr = d_ee->getRepresentative(bse);
          if (d_ee->areDisequal(r, rr, false))
          {
            Trace("cconj-filter") << "...disequal, filtered based on "
                                  << match.toString() << std::endl;
            Trace("cconj-filter") << "lhs: " << r << std::endl;
            Trace("cconj-filter")
                << "rhs: " << d_ee->getRepresentative(bse) << std::endl;
            return true;
          }
          tested++;
          confirmed = confirmed + (r == rr ? 1 : 0);
        }
        eindex--;
      }
      else if (emf[eindex - 1]->isFinished())
      {
        eindex--;
      }
      else if (emf[eindex - 1]->push(tdb, d_ee, match, emf))
      {
        eindex++;
        continue;
      }
      else
      {
        emf[eindex - 1]->pop(match);
      }

      emf.resize(eindex);

      if (!emf.empty())
      {
        emf[eindex - 1]->pop(match);
      }
    } while (!emf.empty());
  }
  if (tested == 0)
  {
    // no tests, reject?
    return true;
  }
  Trace("cconj-filter") << "...success, not filtered, tested=" << tested
                        << ", confirmed=" << confirmed << std::endl;
  return false;
}

bool ConflictConjectureGenerator::filterDeductivelyEntailed(const Node& a,
                                                            const Node& b)
{
  std::unique_ptr<SolverEngine> dentChecker;
  SubsolverSetupInfo ssi(d_env, d_subOptions);
  initializeSubsolver(d_env.getNodeManager(), dentChecker, ssi, true, 100);
  quantifiers::FirstOrderModel* model = d_treg.getModel();
  Trace("cconj-filter") << "Assuming:" << std::endl;
  for (size_t i = 0; i < model->getNumAssertedQuantifiers(); i++)
  {
    Node phi = model->getAssertedQuantifier(i);
    Trace("cconj-filter") << phi << std::endl;
    dentChecker->assertFormula(phi);
  }
  Node lem = a.eqNode(b);
  std::unordered_set<Node> fvs;
  expr::getFreeVariables(lem, fvs);
  std::vector<Node> bvs(fvs.begin(), fvs.end());
  if (!bvs.empty())
  {
    NodeManager* nm = nodeManager();
    lem = nm->mkNode(Kind::FORALL, nm->mkNode(Kind::BOUND_VAR_LIST, bvs), lem);
  }
  lem = lem.notNode();
  dentChecker->assertFormula(lem);
  Trace("cconj-filter") << "Check " << lem << " with subsolver" << std::endl;
  Result r = dentChecker->checkSat();
  Trace("cconj-filter") << "  ...got : " << r << std::endl;
  return (r.getStatus() == Result::UNSAT);
}

void ConflictConjectureGenerator::runFunDefEvaluatorExperiment()
{
  // Putting this here to see if we can provide an ad-hoc definition to the
  // FunDefEvaluator.

  // --Retrieve a reference to the current NodeManager and a reference to the
  // current NodeManager

  NodeManager* node_mgr = nodeManager();

  SkolemManager* sk_mgr = node_mgr->getSkolemManager();

  // --First we create a datatype

  // ----Create a DType instance

  DType my_nat_def("myNat");

  // ----Create the constructor instances

  std::shared_ptr<DTypeConstructor> my_zero_def =
      std::shared_ptr<DTypeConstructor>(new DTypeConstructor("myZ"));

  std::shared_ptr<DTypeConstructor> my_succ_def =
      std::shared_ptr<DTypeConstructor>(new DTypeConstructor("myS"));

  my_succ_def->addArgSelf("myP");

  // ----Add references to these constructors to the DType instance

  my_nat_def.addConstructor(my_zero_def);

  my_nat_def.addConstructor(my_succ_def);

  // ----Transform the DType instance into a TypeNode

  const TypeNode& my_nat = node_mgr->mkDatatypeType(my_nat_def);

  // --Then we declare a function over that datatype

  // ----Create the function type

  const TypeNode& my_plus_typ = node_mgr->mkFunctionType({my_nat, my_nat, my_nat});

  // ----Make a dummy skolem with the function's type

  const Node& my_plus = sk_mgr->mkDummySkolem("my_plus", my_plus_typ);

  // --We create a definition for the function

  // ----Reset my_nat_def to its resolved version

  my_nat_def = my_nat.getDType();

  // ----Fetch the constructors, testers and selectors

  const Node& my_zero = my_nat_def[0].getConstructor();
  const Node& my_is_zero = my_nat_def[0].getTester();
  const Node& my_succ = my_nat_def[1].getConstructor();
  const Node& my_pred = my_nat_def[1].getSelector(0);

  // ----Now construct the entire definition

  // x0
  const Node& x0 = d_tc.getCanonicalFreeVar(my_nat, 0);

  // x1
  const Node& x1 = d_tc.getCanonicalFreeVar(my_nat, 1);

  // e0 := my_pred(x0)
  const Node& e0 = node_mgr->mkNode(Kind::APPLY_SELECTOR, my_pred, x0);

  // e1 := my_plus(my_pred(x0), x1)
  const Node& e1 = node_mgr->mkNode(Kind::APPLY_UF, my_plus, e0, x1);

  // e2 := my_succ(my_plus(my_pred(x0), x1))
  const Node& e2 = node_mgr->mkNode(Kind::APPLY_CONSTRUCTOR, my_succ, e1);

  // e3 := my_is_zero(x0)
  const Node& e3 = node_mgr->mkNode(Kind::APPLY_TESTER, my_is_zero, x0);

  // e4 := ite(my_is_zero(x0), x1, my_succ(my_plus(my_pred(x0), x1)))
  const Node& e4 = node_mgr->mkNode(Kind::ITE, e3, x1, e2);

  // e9 := my_plus(x0, x1)
  Node e9 = node_mgr->mkNode(Kind::APPLY_UF, my_plus, x0, x1);

  // Need to annotate e9 in just the right way for it to be recognized as a definition.
  Node aexpr = node_mgr->mkNode(Kind::INST_ATTRIBUTE, e9);
  aexpr = node_mgr->mkNode(Kind::INST_PATTERN_LIST, aexpr);
  FunDefAttribute fda;
  e9.setAttribute(fda, true);

  // e10 := my_plus(x0, x1) = ite(my_is_zero(x0),
  //                              x1,
  //                              my_succ(my_plus(my_pred(x0), x1)))
  const Node& e10 = node_mgr->mkNode(Kind::EQUAL, e9, e4);

  // [x0, x1]
  const Node& e5 = node_mgr->mkNode(Kind::BOUND_VAR_LIST, x0, x1);

  // forall [x0, x1].
  //   my_plus(x0, x1) = ite(my_is_zero(x0),
  //                         x1,
  //                         my_succ(my_plus(my_pred(x0), x1)))
  const Node& my_plus_def = node_mgr->mkNode(Kind::FORALL, e5, e10, aexpr);

  // --Clear the FunDefEvaluator

  // d_funDefEvaluator.clear();

  // --We add the universally quantified formula to the FunDefEvaluator

  d_funDefEvaluator.assertDefinition(my_plus_def);

  // --We create a term we want to evaluate

  const Node& e6 = node_mgr->mkNode(Kind::APPLY_CONSTRUCTOR, my_zero);
  const Node& e7 = node_mgr->mkNode(Kind::APPLY_CONSTRUCTOR, my_succ, e6);
  const Node& e8 = node_mgr->mkNode(Kind::APPLY_CONSTRUCTOR, my_succ, e7);
  const Node& raw_term = node_mgr->mkNode(Kind::APPLY_UF, my_plus, e8, e7);

  // --We evaluate the term

  const Node& evaled_term = d_funDefEvaluator.evaluateDefinitions(raw_term);

  // --Some printing

  Trace("ccgen-experiment") << "definition is " << my_plus_def << std::endl;
  Trace("ccgen-experiment") << raw_term << " --evaluate--> " << evaled_term << std::endl;

  // -- Done!

  return;
}

void ConflictConjectureGenerator::setUpFunDefEvaluator()
{
  const CDList<Node>& preserved_formulas = d_env.getPreservedFormulas();

  Trace("setUpFunDefEvaluator") << "(preserved-formulas" << std::endl;
  for (const Node& phi : preserved_formulas)
  {
    Trace("setUpFunDefEvaluator") << phi << std::endl;
  }
  Trace("setUpFunDefEvaluator") << ")" << std::endl;

  // Organize preserved formulas by head symbol.  Each preserved formula is
  // expected to have the form:
  //
  //     (forall (VARS ...)
  //       (! (=> TEST (= (HEAD VARS ...) BODY))))
  //

  std::map<Node, std::vector<Node>> head_to_rules;

  for (const Node& phi : preserved_formulas)
  {
    head_to_rules[phi[1][1][0].getOperator()].push_back(phi);
  }

  // if (TraceIsOn("ccgen-preserved"))
  // {
  //   for (std::map<Node, std::vector<Node>>::iterator entry =
  //            head_to_rules.begin();
  //        entry != head_to_rules.end();
  //        entry++)
  //   {
  //     Trace("ccgen-preserved")
  //         << "Rules with head " << entry->first << " are" << std::endl;

  //     for (std::vector<Node>::iterator rule = entry->second.begin();
  //          rule != entry->second.end(); rule++)
  //     {
  //       Trace("ccgen-preserved") << "* " << *rule << std::endl;
  //     }
  //   }
  // }

  // Reconstruct definition for each head function symbol using its associated
  // formulas.

  NodeManager* node_mgr = nodeManager();
  SkolemManager* sk_mgr = node_mgr->getSkolemManager();

  for (std::map<Node, std::vector<Node>>::iterator entry =
           head_to_rules.begin();
       entry != head_to_rules.end();
       entry++)
  {
    // The function symbol for which we want to synthesize a definition.
    const Node& func_sym = entry->first;

    // The function's argument types
    const std::vector<TypeNode>& formal_typs = func_sym.getType().getArgTypes();

    // The variables that serve as the function's formal parameters.  This will
    // serve as the range of each substitution.
    std::vector<Node> formals;

    for (const TypeNode& typ : formal_typs)
    {
      formals.push_back(sk_mgr->mkDummySkolem("x", typ));
    }

    // The current state of the definition we're building.
    Node state = Node::null();

    // Loop over available rules to build state.
    for (const Node& rule : entry->second)
    {
      // Snatch the bound variables of the universally quantified rule and place
      // them in a vector.  This vector will be the substitution's domain.
      const Node& bvs_node = rule[0];

      std::vector<Node> bvs;
      bvs.insert(bvs.end(), bvs_node.begin(), bvs_node.end());

      // Put the domain and range together to make a substitution.
      Subs sigma;

      sigma.add(bvs, formals);

      // Apply the substitution to the body of the universally quantified
      // formula that is rule.
      const Node& body = sigma.apply(rule[1]);

      // Retrieve the test after the substitution.
      const Node& test = body[0];

      // Retrieve the rhs after the substitution.
      const Node& rhs = body[1][1];

      // Update the state
      if (state.isNull())
      {
        state = rhs;
      }
      else
      {
        state = node_mgr->mkNode(Kind::ITE, test, rhs, state);
      }
    }

    // func_sym(formals ...), then annotations.
    std::vector<Node> func_app_children{func_sym};

    func_app_children.insert(func_app_children.end(), formals.begin(), formals.end());

    Node func_app = node_mgr->mkNode(Kind::APPLY_UF, func_app_children);

    Node attr_expr = node_mgr->mkNode(Kind::INST_ATTRIBUTE, func_app);

    attr_expr = node_mgr->mkNode(Kind::INST_PATTERN_LIST, attr_expr);

    FunDefAttribute fun_def_attr;

    func_app.setAttribute(fun_def_attr, true);

    // func_sym(formals ...) == state
    const Node& func_rule = node_mgr->mkNode(Kind::EQUAL, func_app, state);

    // forall (formals ...). func_sym(formals ...) == state
    const Node& func_defn =
        node_mgr->mkNode(Kind::FORALL,
                         node_mgr->mkNode(Kind::BOUND_VAR_LIST, formals),                         
                         func_rule, attr_expr);

    // Submit definition to FunDefEvaluator instance.
    d_funDefEvaluator.assertDefinition(func_defn);
  }

  d_set_up_fun_def_evaluator = true;
}

bool ConflictConjectureGenerator::filterEvalsToFalse(const Node& lhs,
                                                     const Node& rhs)
{
  Trace("ccgen-filter-eval")
      << "* * * * *" << std::endl
      << "looking at " << lhs << " == " << rhs << std::endl;

  // We already set up the FunDefEvaluator in check() as d_funDefEvaluator.

  // Collect all free variables in (lhs == rhs) as a vector with no repetitions.

  std::unordered_set<Node> fvs_set;
  expr::getFreeVariables(lhs, fvs_set);
  expr::getFreeVariables(rhs, fvs_set);
  std::vector<Node> fvs;
  fvs.insert(fvs.end(), fvs_set.begin(), fvs_set.end());

  if (TraceIsOn("ccgen-filter-eval"))
  {
    Trace("ccgen-filter-eval") << "with free variables {";
    bool first_time = true;
    for (const Node& fv : fvs)
    {
      if (first_time)
      {
        first_time = false;
      }
      else
      {
        Trace("ccgen-filter-eval") << ", ";
      }
      Trace("ccgen-filter-eval") << fv;
    }
    Trace("ccgen-filter-eval") << "}" << std::endl;
  }

  // Prepare the grammar for enumerating tuples of free variables.

  //   This dictionary will map each free variable type to a grammar.

  std::map<TypeNode, SygusGrammar> typ_to_gr;

  //   Let's populate the dictionary with the initial version of each type's grammar.

  for (const Node& fv : fvs)
  {
    const TypeNode& typ = fv.getType();

    if (typ_to_gr.find(typ) == typ_to_gr.end())
    {
      typ_to_gr.emplace(std::make_pair(
          typ, SygusGrammarCons::mkDefaultGrammar(d_env, typ, Node::null())));
    }
  }

  //   The grammars have unwanted production rules and need to be cleaned up.
  //   For datatype-sorted non-terminals we remove any rule with kind ITE or
  //   APPLY_SELECTOR.  For non-terminals of other types we remove all rules and
  //   replace them with the 'any constant' rule.

  for (std::map<TypeNode, SygusGrammar>::iterator typ_gr_pair =
           typ_to_gr.begin();
       typ_gr_pair != typ_to_gr.end();
       typ_gr_pair++)
  {
    SygusGrammar& gr = typ_gr_pair->second;

    // Collect all the rules that we need to remove from the grammar.

    std::vector<std::pair<Node, Node>> rules_to_remove;

    for (const Node& nt : gr.getNtSyms())
    {
      for (const Node& rule : gr.getRulesFor(nt))
      {
        if (nt.getType().isDatatype())
        {
          if (rule.getKind() == Kind::ITE
              || rule.getKind() == Kind::APPLY_SELECTOR)
          {
            rules_to_remove.emplace_back(std::pair<Node, Node>{nt, rule});
          }
        }
        else
        {
          rules_to_remove.emplace_back(std::pair<Node, Node>{nt, rule});
        }
      }
    }

    // Remove all the rules as intended.

    for (std::vector<std::pair<Node, Node>>::iterator nt_rule_pair =
             rules_to_remove.begin();
         nt_rule_pair != rules_to_remove.end();
         nt_rule_pair++)
    {
      gr.removeRule(nt_rule_pair->first, nt_rule_pair->second);
    }

    // Add 'any constant' rules for non-terminals that have types that are not
    // inductive datatypes.

    for (const Node& nt : gr.getNtSyms())
    {
      const TypeNode& typ = nt.getType();

      if (!typ.isDatatype())
      {
        gr.addAnyConstant(nt, typ);
      }
    }
  }

  //   Isolate the root non-terminal for each argument's grammar.  For example, I
  //   expect type T's grammar to have exactly one non-terminal of type T.  This
  //   non-terminal is treated as the start non-terminal.

  std::map<TypeNode, Node> typ_to_nt;

  for (auto entry : typ_to_gr)
  {
    TypeNode typ = entry.first;

    for (auto nt : entry.second.getNtSyms())
    {
      if (nt.getType() == typ)
      {
        typ_to_nt[typ] = nt;

        break;
      }
    }
  }

  //   We need to construct the type of n-tuples, the "root" type.

  std::vector<TypeNode> elt_typs;

  for (const Node& fv : fvs)
  {
    elt_typs.push_back(fv.getType());
  }

  const TypeNode& rt_typ = nodeManager()->mkTupleType(elt_typs);

  //   We then manufacture a dummy skolem of the root type.

  Node rt_nt =
      nodeManager()->getSkolemManager()->mkDummySkolem("root_nt", rt_typ);

  //   Collect all the non-terminals -- all non-terminals across all argument
  //   grammars as well as the non-terminal for the tuple -- in a "master list".

  std::vector<Node> all_nts{rt_nt};

  for (auto entry : typ_to_gr)
  {
    std::vector<Node> gr_nts = entry.second.getNtSyms();
    all_nts.insert(all_nts.end(), gr_nts.begin(), gr_nts.end());
  }

  //   Use all_nts to construct the root grammar.

  SygusGrammar rt_gr(std::vector<Node>{}, all_nts);

  //   Make the sole production rule for rt_nt.  To do this we need to grab the
  //   sole constructor of the datatype rt_typ and apply the constructor to the
  //   non-terminal for each type in elt_typ.

  std::vector<Node> rt_rule_children{ rt_typ.getDType()[0].getConstructor() };

  for (const TypeNode& typ : elt_typs)
  {
    rt_rule_children.push_back(typ_to_nt[typ]);
  }

  Node rt_rule = nodeManager()->mkNode(Kind::APPLY_CONSTRUCTOR, rt_rule_children);

  //   Associate rt_rule with rt_nt in rt_gr.

  rt_gr.addRule(rt_nt, rt_rule);

  //   Add all rules for all non-terminals across all argument grammars to the
  //   root grammar.

  for (auto entry : typ_to_gr)
  {
    SygusGrammar gr = entry.second;

    for (auto nt : gr.getNtSyms())
    {
      for (auto rule : gr.getRulesFor(nt))
      {
        rt_gr.addRule(nt, rule);
      }
    }
  }

  //   Before we resolve the grammar let's make sure we have exactly what we need
  //   by printing all its non-terminals and associated rules.

  if (TraceIsOn("ccgen-filter-eval"))
  {
    Trace("ccgen-filter-eval")
        << "Here are rules for each non-terminal." << std::endl;
    for (auto nt : rt_gr.getNtSyms())
    {
      Trace("ccgen-filter-eval") << "* " << nt << ":" << std::endl;
      for (auto rule : rt_gr.getRulesFor(nt))
      {
        Trace("ccgen-filter-eval") << "  * " << rule << std::endl;
      }
    }
  }

  //   We need to resolve the grammar, quitting early if resolution fails.

  const TypeNode& rt_gr_typ = rt_gr.resolve();

  Assert(rt_gr.isResolved());

  // Initialize the SygusTermEnumerator class.

  SygusTermEnumerator rt_gr_enum(d_env, rt_gr_typ);

  // Enumerate a number of tuples and therefore substitutions.

  //   We need to retrieve or decide the number of tuples to generate.

  size_t limit = 10;

  //   Let's generate the limit-many substitution ranges (tuples).

  std::vector<Node> rngs;

  size_t n_rngs = 0;

  bool first_time = n_rngs < limit;

  while (first_time || (n_rngs < limit && rt_gr_enum.increment()))
  {
    if (first_time)
    {
      first_time = false;
    }

    const Node& next_rng = rt_gr_enum.getCurrent();

    if (!next_rng.isNull())
    {
      rngs.push_back(next_rng);

      n_rngs++;
    }
  }

  if (TraceIsOn("ccgen-filter-eval"))
  {
    Trace("ccgen-filter-eval")
        << "Generated substitution ranges:" << std::endl;

    for (const Node& rng : rngs)
    {
      Trace("ccgen-filter-eval") << "* " << rng << std::endl;
    }
  }

  // Apply the substitutions, evaluate the terms, and check whether equality is
  // entailed.

  //   Make an instance of cvc5::internal::Subs, then use the apply() method.
  //   Let's see if we can extract the range of the substitution somehow.
  //   You want to produce rng_args from rng by scrapping the constructor.
  //   You'll use add(fvs, ???)

  // EntailmentCheck* ent_chk = d_treg.getEntailmentCheck();

  for (const Node& rng : rngs)
  {
    Subs sigma;

    // This is rng as a vector instead of a tuple.  We can't feed a tuple to sigma.
    std::vector<Node> rng_args;
    rng_args.insert(rng_args.end(), rng.begin(), rng.end());

    sigma.add(fvs, rng_args);

    // image of lhs under sigma
    const Node& lhs_img = sigma.apply(lhs);

    // Trace("ccgen-filter-eval") << "!! just about to evaluate " << lhs << " !!" << std::endl;

    // reduced lhs
    const Node& lhs_red = d_funDefEvaluator.evaluateDefinitions(lhs_img);

    // Trace("ccgen-filter-eval") << "!! just about to retrieve entailed term for " << lhs_red << " !!" << std::endl;

    // representative of lhs
    // const Node& lhs_rep = d_ee->getRepresentative(ent_chk->getEntailedTerm(lhs_red));

    // same for rhs

    const Node rhs_img = sigma.apply(rhs);

    // Trace("ccgen-filter-eval") << "!! just about to evaluate " << rhs << " !!" << std::endl;

    const Node& rhs_red = d_funDefEvaluator.evaluateDefinitions(rhs_img);

    // Trace("ccgen-filter-eval") << "!! just about to retrieve entailed term for " << rhs_red << " !!" << std::endl;

    // const Node& rhs_rep = d_ee->getRepresentative(ent_chk->getEntailedTerm(rhs_red));

    // Trace("ccgen-filter-eval") << "!! retrieved !!" << std::endl;

    Trace("ccgen-filter-eval") << "checking whether " << lhs_img << " == " << rhs_img << "... ";

    if (lhs_red == rhs_red)
    {
      Trace("ccgen-filter-eval") << "entailment check says yes." << std::endl;
    }
    else
    {
      Trace("ccgen-filter-eval") << "entailment check says no." << std::endl << std::endl;

      return true;
    }
  }

  // If equality is always entailed we return false and quit.

  Trace("ccgen-filter-eval") << "all equal!" << std::endl << std::endl;

  return false;
}

/**
 * `filterManual()` expects two inputs.  The first is the body of a candidate
 * conjecture.  The second is the number of substitutions with which the
 * conjecture has been confirmed.  We print the candidate conjecture for the
 * user and ask if it should be considered.  If it should, we ask if it should
 * be assumed or it should be proved.  We also ask if the conjecture generator
 * should be turned off after.  On the other hand if we choose to ignore the
 * conjecture we return `true`, as in 'yes, throw away this conjecture', and
 * leave it at that.
 *
 * Let's expand all the abbreviated variable names in this function.  conj_body
 * is 'body of conjecture', fvs_set is 'free variables as a set', fvs is 'free
 * variables', bvs is 'bound variables', and conj is 'conjecture'.
 */
bool ConflictConjectureGenerator::filterManual(const Node conj_body, int tested)
{
  NodeManager* node_mgr = nodeManager();

  // Construct the universally quantified conjecture from the conjecture's body.
  std::unordered_set<Node> fvs_set{};
  expr::getFreeVariables(conj_body, fvs_set);
  std::vector<Node> fvs{};
  fvs.insert(fvs.end(), fvs_set.begin(), fvs_set.end());
  const Node bvs = node_mgr->mkNode(Kind::BOUND_VAR_LIST, fvs);
  Node lem = node_mgr->mkNode(Kind::FORALL, bvs, conj_body);

  // Keep conjecture?
  {
    // pb --> 'prompt builder'.
    std::ostringstream pb;
    pb << "Should the following conjecture with score " << tested << " be kept?" << std::endl << lem << std::endl << "[Y/N]: ";

    if (!promptForYesOrNo(pb.str()))
    {
      // User said 'no' so discard the conjecture.
      return true;
    }
  }

  // Transform conjecture?
  {
    std::cout << "What should we do?" << std::endl << "[0: Assume conjecture | 1: Prove conjecture | 2: Send splitting lemma] ";

    std::string resp;
    std::getline(std::cin, resp);

    if (resp.size() > 0 && resp[0] == '0')
    {
    }
    else if (resp.size() > 0 && resp[0] == '1')
    {
      lem = lem.negate();
    }
    else if (resp.size() > 0 && resp[0] == '2')
    {
      lem = lem.orNode(lem.negate());
    }
    else
    {
      Assert(false);
    }
  }

  // Assume conjecture?
  // {
  //   std::ostringstream pb;
  //   pb << "Should we assume that the conjecture holds?  Otherwise we'll try to prove it. " << std::endl << "[Y/N]: ";

  //   if (!promptForYesOrNo(pb.str()))
  //   {
  //     // User wants us to prove the conjecture, so let's negate it.
  //     lem = lem.negate();
  //   }
  // }

  // Turn off generator?
  {
    std::ostringstream pb;
    pb << "Should we turn off the conjecture generator?" << std::endl << "[Y/N]: ";

    if(promptForYesOrNo(pb.str()))
    {
      d_switched_off = true;

      // std::ofstream* inference_stream = d_env.getInferenceStream();
      // (*inference_stream) << "********************************************************************************" << std::endl;
    }
  }

  // Send lemma with no phase requirement.
  d_qim.addPendingLemma(lem, InferenceId::QUANTIFIERS_CONFLICT_CONJ_GEN_SPLIT);

  // Discard the conjecture unconditionally.
  return true;
}

bool ConflictConjectureGenerator::promptForYesOrNo(std::string prompt) const
{
  // Print the prompt to standard output.
  std::cout << prompt;

  // Read a line from standard input.
  std::string resp_str;
  std::getline(std::cin, resp_str);

  // Use the user's response string to determine the response boolean.
  bool resp = false;
  if (resp_str.size() > 0 && resp_str[0] == 'Y')
  {
    resp = true;
  }

  return resp;
}

bool ConflictConjectureGenerator::filterInductivelyEntailed(const Node& conj_body)
{
  std::unique_ptr<SolverEngine> induction_prover;

  Options ind_prov_opts;
  ind_prov_opts.copyValues(d_subOptions);
  ind_prov_opts.write_quantifiers().dtStcInduction = true;
  smt::SetDefaults::disableChecking(ind_prov_opts);

  SubsolverSetupInfo ssi(d_env, ind_prov_opts);

  initializeSubsolver(d_env.getNodeManager(), induction_prover, ssi, true, 1000);

  quantifiers::FirstOrderModel* model = d_treg.getModel();
  for (size_t i = 0; i < model->getNumAssertedQuantifiers(); i++)
  {
    const Node phi = model->getAssertedQuantifier(i);
    induction_prover->assertFormula(phi);
  }

  NodeManager* node_mgr = nodeManager();
  std::unordered_set<Node> fvs_set{};
  expr::getFreeVariables(conj_body, fvs_set);
  std::vector<Node> fvs{};
  fvs.insert(fvs.end(), fvs_set.begin(), fvs_set.end());
  const Node bvs = node_mgr->mkNode(Kind::BOUND_VAR_LIST, fvs);
  Node lem = node_mgr->mkNode(Kind::FORALL, bvs, conj_body);
  lem = lem.negate();

  induction_prover->assertFormula(lem);

  Result r = induction_prover->checkSat();
  Trace("filterProvable") << "(induction " << lem << " " << r << ")" << std::endl;

  // Candidate conjecture is inductively entailed.
  return (r.getStatus() == Result::UNSAT);
}

void ConflictConjectureGenerator::debugPrintGenTrie(GenTrie& gt)
{
  struct Job
  {
    std::vector<Node> d_path;
    const GenTrie d_gt;
  };

  std::vector<Job> jobs;
  jobs.push_back({Job{std::vector<Node>{}, gt}});

  // The front of the job queue.  The back of the job queue is jobs.size().
  // When the two are equal the job queue is empty.
  size_t front = 0;

  Trace("ConflictConjectureGenerator::d_gtrie") << "(d_gtrie " << std::endl;
  while (front != jobs.size())
  {
    Job job = jobs[front];
    ++front;

    std::vector<Node> curr_path = job.d_path;
    GenTrie curr_gt = job.d_gt;

    Trace("ConflictConjectureGenerator::d_gtrie") << "(path";
    for (const Node& av : curr_path)
    {
      Trace("ConflictConjectureGenerator::d_gtrie") << " " << av;
    }
    Trace("ConflictConjectureGenerator::d_gtrie") << ") ";

    Trace("ConflictConjectureGenerator::d_gtrie") << "(generalizations";
    for (const std::pair<Node, Node>& entry : curr_gt.d_gens)
    {
      Trace("ConflictConjectureGenerator::d_gtrie") << " " << std::get<0>(entry);
    }
    Trace("ConflictConjectureGenerator::d_gtrie") << ")" << std::endl;

    for (const std::pair<Node, GenTrie> entry : curr_gt.d_children)
    {
      std::vector<Node> new_path;
      new_path.insert(new_path.begin(), curr_path.begin(), curr_path.end());
      new_path.push_back(std::get<0>(entry));

      jobs.push_back(Job{new_path, std::get<1>(entry)});
    }
  }
  Trace("ConflictConjectureGenerator::d_gtrie") << ")" << std::endl;
}

void ConflictConjectureGenerator::findCongruenceCandidates()
{
  std::unordered_set<Node> source;
  source.insert(d_conjBuffer.begin(), d_conjBuffer.end());
  std::unordered_set<Node> to_remove;
  std::unordered_set<Node> to_add;
  bool at_fixed_point = false;

  while (!at_fixed_point)
  {
    at_fixed_point = true;

    for (const Node& cand : source)
    {
      const Node& lhs = cand[0];
      const Node& rhs = cand[1];

      if (!lhs.hasOperator() || !rhs.hasOperator())
      {
        continue;
      }

      const Node& lhs_op = lhs.getOperator();
      const Node& rhs_op = rhs.getOperator();

      if (lhs_op != rhs_op)
      {
        continue;
      }

      if (lhs.getKind() == Kind::APPLY_UF)
      {
        std::vector<size_t> positions;
        for (size_t i = 0; i < lhs.getNumChildren(); ++i)
        {
          if (lhs[i] != rhs[i])
          {
            positions.push_back(i);
          }
        }
        if (positions.size() != 1)
        {
          continue;
        }
        const size_t position = positions[0];
        if (!lhs[position].getType().isDatatype())
        {
          continue;
        }
        to_add.insert(lhs[position].eqNode(rhs[position]));
        at_fixed_point = false;
      }
      else if (lhs.getKind() == Kind::APPLY_CONSTRUCTOR)
      {
        std::vector<size_t> positions;
        bool skip = false;
        for (size_t i = 0; i < lhs.getNumChildren(); ++i)
        {
          if (lhs[i].getType().isDatatype())
          {
            if (lhs[i] != rhs[i])
            {
              positions.push_back(i);
            }
          }
          else if (lhs[i] != rhs[i])
          {
            skip = true;
          }
        }
        if (skip)
        {
          continue;
        }
        else
        {
          for (const size_t i : positions)
          {
            to_add.insert(lhs[i].eqNode(rhs[i]));
          }
          to_remove.insert(cand);
          at_fixed_point = false;
        }
      }
    }
    source.clear();
    source.insert(to_add.begin(), to_add.end());
    d_conjBuffer.insert(to_add.begin(), to_add.end());
    to_add.clear();
  }

  for (const Node& cand : to_remove)
  {
    d_conjBuffer.erase(cand);
  }
  to_remove.clear();
}

const Node& Decision::getPat()
{
  return d_pat;
}

/**
 * This is the constructor for the `Decision` class.  As stated in the header
 * file, it represents our intent to find a substitution `subs` such that the
 * current equality engine `ee` entails that under the substitution `subs`, the
 * pattern `pat` is in the equivalence class representated by `rep`.
 *
 * This function expects that `term_db` is a pointer to the current term
 * database, `ee` is a pointer to the current equality engine, `pat` is a term
 * constructed with user-declared function symbols, constructor symbols and
 * equivalence class variables, and finally that `rep` is the representative of
 * some equivalence class.  It is also expected that `pat` is a node with an
 * operator, in other words it's not an equivalence class variable.  It is
 * **not** expected that `pat` or any of its subterms are known to the equality
 * engine, even if they are variable-free.  If for whatever reason we intend to
 * ask the solver for the equivalence class representative of a particular child
 * of `pat` we need to ensure that the child is known to the equality engine.
 *
 * To recap, let 'P' denote the set of subterms of `pat` that are themselves
 * patterns i.e. contain equivalence class variables.  This e-matching algorithm
 * works by associating each element in 'P' with a specific member of a specific
 * equivalence class.  Each instance of `Decision` represents one such
 * association where the subterm of `pat` is stored in `d_pat`, the equivalence
 * class is left implicit, and we are trying to associate `d_pat` with
 * `d_cands[d_next - 1]`.  The elements of `d_cands` are exactly the members of
 * the implicit equivalence class that (1) have the same operator, and (2) agree
 * with `d_pat` on all non-variable children.
 *
 * It behooves us to note the following.  Let `par_dec` (parent decision) be an
 * instance of `Decision`.  We know it represents our intent to match
 * `par_dec.d_pat` (call this 'p') with `par_dec.d_cands[par_dec.d_next - 1]`
 * (call this 't').  It also implies that we intend to match the 'i' th child of
 * 'p' with the representative of the equivalence class of the corresponding
 * child of 't'.  This dictates what the 'descendants' of `par_dec` will look
 * like, and these descendants are created when we run `par_dec.push()`.
 *
 * This function uses a few local variables.  These merit some explanation.
 *
 * `op` is the operator of `pat`.  It's expected to be a user-declared
 * uninterpreted function symbol or a constructor symbol.  It will be used when
 * populating `d_cands`.
 *
 * `ground_args` is a list of pairs.  It starts off empty.  Once we populate it,
 * we expect that it contains a pair (`i`, `t`) if and only if `pat[i]` is free
 * of equivalence class variables.  The nature of `t` depends on whether
 * `pat[i]` exists in the equality engine.  If it exists, we expect `t` to be
 * the representative of the equivalence class of `pat[i]`.  In case `t` doesn't
 * exist in the equality engine, we expect `t` to be exactly `pat[i]`.
 * `ground_args`, too, will be used when populating `d_cands`.
 */
Decision::Decision(TermDb* term_db, eq::EqualityEngine* ee, Node pat, Node rep, Decision* dec, bool consider)
{
  d_pat = pat;
  d_next = 0;
  d_rec_args = std::vector<size_t>{};
  d_var_args = std::vector<size_t>{};
  std::map<size_t, Node> ground_args{};

  // The following loop populates `d_rec_args`, `d_var_args`, and `ground_args`.  

  // n_args --> number of arguments
  const size_t n_args = d_pat.getNumChildren();
  for (size_t i = 0; i < n_args; i++)
  {
    // c --> child
    const Node c = d_pat[i];

    if (c.getKind() == Kind::BOUND_VARIABLE)
    {
      // `c` is a matchable (equivalence class) variable.
      d_var_args.push_back(i);
    }
    else if (!expr::hasBoundVar(c))
    {
      // `c` is free of equivalence class variables.
      if (ee->hasTerm(c))
      {
        ground_args[i] = ee->getRepresentative(c);
      }
      else
      {
        ground_args[i] = c;
      }
    }
    else
    {
      // `c` is a non-variable subterm of `pat` that is itself a pattern.
      d_rec_args.push_back(i);
    }
  }

  // The following loop populates `d_cands`.  Once we're out of the loop we
  // expect that a term is in `d_cands` if and only if all these conditions are
  // satisfied (1) it is a member of the equivalence class of `rep`, (2) its
  // operator is `op`, (3) it is 'active', and (4) it agrees with `d_pat` on all
  // variable-free terms.
  //
  // **Note**.  I need to understand what 'active' means.  According to Andy the
  // restriction to active terms "will filter terms that are congruent to
  // another term we have already considered."

  Assert(d_pat.hasOperator());
  // op --> operator.
  const Node& op = d_pat.getOperator();

  // mem_it --> iterator for members of equivalence class.
  eq::EqClassIterator mem_it = eq::EqClassIterator(rep, ee);
  while (!mem_it.isFinished())
  {
    // mem --> member of equivalence class.
    const Node& mem = *mem_it;

    ++mem_it;

    if (!mem.hasOperator() || mem.getOperator() != op || !term_db->isTermActive(mem))
    {
      // No point adding `mem` to `d_cands`.
      continue;
    }

    // The following loop ensures condition (4) stated above.

    // Should we add `mem` to `d_cands`?  So far, yes.  We'll change this to
    // `false` if necessary.
    bool accept = true;

    // ent --> entry.
    for (const std::pair<const size_t, Node>& ent : ground_args)
    {
      // i --> index of ground child of `pat`.
      const size_t i = std::get<0>(ent);

      // rgp --> representative of ground child of `pat`.
      const Node& rgp = std::get<1>(ent);

      // rgm --> representative of ground child of `mem`.
      const Node& rgm = ee->getRepresentative(mem[i]);

      if (rgp != rgm)
      {
        // `pat` and `mem` disagree on a ground term.  We shouldn't add `mem` to
        // `d_cands`.
        accept = false;
        break;
      }
    }

    if (accept)
    {
      // No problems thus far.  Add `mem` to `d_cands`.
      d_cands.push_back(mem);
    }
  }
}

bool Decision::push(TermDb* term_db, eq::EqualityEngine* ee, Subs& subs, Trail& decs) 
{
  if (isFinished())
  {
    // Trace("cconjGen") << " \"out\")" << std::endl;

    // If there are no more members in the equivalence class associated
    // with this instance that could match `d_pat` then we have to fail.
    return false;
  }

  // The variable-free term we're going to match `d_pat` against.  The
  // name 'cand' is short for 'candidate term'.
  const Node& cand = d_cands[d_next];

  // `d_next` always stores the index of the *next* candidate term so
  // we bump it now.
  d_next++;

  // We add a new mapping to `subs` for each child of `d_pat` that
  // happens to be a variable.  For each `i` in `d_var_args` we want
  // to extend `subs` by mapping `d_pat[i]` to term `cand[i]`.
  for (const size_t i : d_var_args)
  {
    // The variable for which we want to add a mapping.  'var' is
    // short for 'variable'.
    const Node& var = d_pat[i];

    // The term to which `var` is mapped in `subs`.  If `var` is
    // unmapped then `cur` is `Node::null()`.  'cur' is short for
    // 'current mapping'.
    const Node& cur = subs.getSubs(var);

    if (cur.isNull())
    {
      // `var` does not have a mapping in `subs`.  We can map `var` to
      // `cand[i]` without a second thought.  We should also update
      // `d_bound`.  If we need to backtrack `subs`, `pop()` will
      // remove exactly the variables at indices `d_bound`.
      subs.add(var, cand[i]);
      d_bound.insert(i);
    }
    else
    {
      // `var` is already mapped to `cur` in `subs`.  If `cur` and
      // `cand[i]` are equivalent, we don't need to do any work.  If
      // they are not equivalent then matching has failed, so we must
      // return `false`.
      if (ee->areEqual(cur, cand[i]))
      {
        continue;
      }
      else
      {
        // Trace("cconjGen") << " \"out\")" << std::endl;

        // We will not backtrack yet.  Instead we'll leave it up to the
        // caller, `filterEmatching()`, to call `pop()` after we return
        // `false`.
        return false;
      }
    }
  }

  // Remember that e-matching is a recursive process.  This function,
  // `push()`, isn't recursive.  Instead it queues fresh e-matching
  // jobs on to `decs` in the form of fresh `Decision` instances.
  // Each child of `d_pat` that is a non-variable pattern is one of
  // the two pieces of data needed to create such an instance of
  // `Decision`.  The second piece is the equivalence class
  // representative of the corresponding child of `cand`.  We will
  // collect these representatives in the vector `reps_rec` below.
  // The name 'reps_rec' is short for 'representatives for recursive
  // calls'.
  //
  // Here's a another attempt to explain the logic.  Since `d_pat[i]`
  // is an operator application that contains a variable as a proper
  // subterm we need to search through all the terms in `rep`, the
  // equivalence class of `cand[i]`.  `d_pat[i]` has the form f(a_1,
  // ..., a_n) and `rep` contains the term f(t_1, ..., t_n).  To check
  // whether the latter term matches the former pattern we need to
  // perform at most n-many additional searches, one for each child
  // that is a non-variable pattern.
  std::vector<Node> reps_rec{};

  for (const size_t i : d_rec_args)
  {
    Trace("Decision-push") << "before call to getRepresentative() in push()" << std::endl;
    // 'rep' is short for 'representative'.
    const Node& rep = ee->getRepresentative(cand[i]);
    Trace("Decision-push") << "after call to getRepresentative() in push()" << std::endl;

    // TODO.  The following criterion is taken from Andy's code.  I
    // don't know why he's checking this.  I should ask why
    // `isConst()` is important.
    if (!rep.isConst())
    {
      // Trace("cconjGen") << " \"out\")" << std::endl;

      return false;
    }

    reps_rec.emplace_back(rep);
  }

  // Let's actually construct and queue up the recursive jobs, which
  // are represented by instances of `Decision`.

  // it_no is 'iteration number'
  // size_t it_no = 0;

  // 'n_rec_args' is short for 'number of arguments for recursive calls'.
  const size_t n_rec_args = d_rec_args.size();
  for (size_t i = 0; i < n_rec_args; i++)
  {
    // ++it_no;
    decs.emplace_back(new Decision(term_db, ee, d_pat[d_rec_args[i]], reps_rec[i], this, true));
  }

  return true;
}

void Decision::pop(Subs& subs)
{
  // Read description in header file.

  for (const size_t i : d_bound)
  {
    subs.erase(d_pat[i]);
  }

  d_bound.clear();
}

bool Decision::isFinished() const
{
  // Read description in header file.

  return d_next == d_cands.size();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
