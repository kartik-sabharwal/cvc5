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
  d_false = nodeManager()->mkConst(false);

  d_subOptions.copyValues(options());
  d_subOptions.write_quantifiers().instMaxRounds = 5;
  d_subOptions.write_quantifiers().quantInduction = false;
  d_subOptions.write_quantifiers().dtStcInduction = false;
  d_subOptions.write_quantifiers().conjectureGen = false;
  d_subOptions.write_quantifiers().contextualEnumerator = false;
  d_subOptions.write_quantifiers().conflictConjectureGen = false;
  smt::SetDefaults::disableChecking(d_subOptions);
}

void ConflictConjectureGenerator::presolve() {}

bool ConflictConjectureGenerator::needsCheck(Theory::Effort e)
{
  return e >= Theory::EFFORT_LAST_CALL;
}

void ConflictConjectureGenerator::reset_round(Theory::Effort e) {}

void ConflictConjectureGenerator::registerQuantifier(Node q) {}

void ConflictConjectureGenerator::checkOwnership(Node q) {}

QuantifiersModule::QEffort ConflictConjectureGenerator::needsModel(
    Theory::Effort e)
{
  return QEFFORT_STANDARD;
}

void ConflictConjectureGenerator::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e != QEFFORT_STANDARD)
  {
    return;
  }

  buildGrammarFromContext();

  return;
  
  Trace("cconj") << "ConflictConjectureGenerator: check" << std::endl;
  
  // update the function definitions
  d_funDefEvaluator.clear();
  quantifiers::FirstOrderModel* model = d_treg.getModel();
  Trace("ccgen-debug") << "Refresh function definitions..." << std::endl;
  std::unordered_set<Node> qsyms;
  std::unordered_set<TNode> qvisited;
  for (size_t i = 0; i < model->getNumAssertedQuantifiers(); i++)
  {
    Node phi = model->getAssertedQuantifier(i);
    Trace("ccgen-debug") << "- quant : " << phi << std::endl;

    // if (d_qreg.getQuantAttributes().isFunDef(phi))
    // {
    //   Trace("ccgen-debug") << "  fun def: " << phi << std::endl;
    //   d_funDefEvaluator.assertDefinition(phi);
    // }

    // record symbols
    expr::getSymbols(phi, qsyms, qvisited);
  }
  setUpFunDefEvaluator();

  d_ee = d_qstate.getEqualityEngine();
  d_eqcGen.clear();
  d_eqcGenRec.clear();
  std::vector<Node> candDeq;
  eq::EqClassIterator eqc = eq::EqClassIterator(d_false, d_ee);
  while (!eqc.isFinished())
  {
    Node n = *eqc;
    if (n.getKind() == Kind::EQUAL)
    {
      candDeq.push_back(n);
    }
    ++eqc;
  }

  Trace("ccgen") << "...found " << candDeq.size() << " candidate disequalities"
                 << std::endl;
  for (const Node& eq : candDeq)
  {
    Trace("ccgen-debug") << "- disequality: " << eq << std::endl;
    std::unordered_set<Node> syms;
    expr::getSymbols(eq, syms);
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
    checkDisequality(eq);
  }

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
    lem = nm->mkNode(Kind::OR, lem.negate(), lem);
    Trace("ccgen-lemma") << "ConflictConjectureGenerator: send lemma " << lem
                         << std::endl;
    d_qim.addPendingLemma(lem,
                          InferenceId::QUANTIFIERS_CONFLICT_CONJ_GEN_SPLIT);
    d_conjGenIndex = d_conjGenIndex.get() + 1;
  }
  Trace("cconj") << "ConflictConjectureGenerator: end check" << std::endl;
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
  Trace("ccgen") << "checkDisequality " << eq << std::endl;
  std::vector<Node> vars;
  for (size_t i = 0; i < 2; i++)
  {
    Node r = d_ee->getRepresentative(eq[i]);
    Node v = getOrMkVarForEqc(r);
    vars.push_back(v);
    getGeneralizations(v);
  }
  // see if any generalization of the right hand
  std::vector<Node>& genRhs = d_eqcGenRec[vars[1]];

  Trace("ccgen") << "- look at " << genRhs.size()
                 << " recursive generalizations of RHS" << std::endl;
  // generate the candidates, store in d_conjBuffer
  for (const Node& g : genRhs)
  {
    const std::vector<Node>& gfvs = d_genToFv[g];
    Trace("ccgen-debug") << "  - " << g << std::endl;
    State s = gfvs.empty() ? State::SUBSET : State::UNKNOWN;
    findCompatible(g, gfvs, vars[0], &d_gtrie, s, 0);
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

  // Recall that this class maintains a 

  // Node 2.  This function expands the 
  
  // We will find
  size_t depth = 3;
  
  Node cur = v;
  // the current free variables of cur
  std::vector<Node> fvs;
  std::vector<Node>& grecs = d_eqcGenRec[v];
  fvs.push_back(v);
  Subs subs;
  size_t rindex = Random::getRandom().pick(0, fvs.size() - 1);
  for (size_t i = 0; i < depth; i++)
  {
    Node vc = fvs[rindex];
    Trace("ccgen-debug-expand") << "process " << vc << std::endl;
    Assert(d_bvToEqc.find(vc) != d_bvToEqc.end());
    const std::vector<Node>& gens = getGenForEqc(d_bvToEqc[vc]);

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
     
    if (gens.empty())
    {
      rindex = rindex + 1 == fvs.size() ? 0 : rindex + 1;
      Trace("ccgen-debug") << "...no generalizations" << std::endl;
      // nothing to generalize
      continue;
    }
    size_t gindex = Random::getRandom().pick(0, gens.size() - 1);
    Node g = gens[gindex];
    Node gs = subs.apply(g);
    if (expr::hasSubterm(gs, v))
    {
      Trace("ccgen-debug") << "...cyclic to " << gs << std::endl;
      rindex = Random::getRandom().pick(0, fvs.size() - 1);
      // cyclic, skip
      continue;
    }
    Trace("ccgen-debug-expand") << "...expand to " << gs << std::endl;
    std::vector<Node> newVars;
    if (g.getNumChildren() > 0)
    {
      bool isDag = false;
      for (const Node& gv : g)
      {
        if (subs.contains(gv))
        {
          // already handled
          isDag = true;
        }
        else if (std::find(fvs.begin(), fvs.end(), gv) == fvs.end())
        {
          newVars.push_back(gv);
        }
        else
        {
          // already in progress of being handled
          isDag = true;
        }
      }
      if (isDag)
      {
        rindex = Random::getRandom().pick(0, fvs.size() - 1);
        continue;
      }
    }
    fvs.erase(fvs.begin() + rindex);
    for (const Node& gv : newVars)
    {
      auto it = std::lower_bound(fvs.begin(), fvs.end(), gv);
      fvs.insert(it, gv);
    }
    Trace("ccgen-debug") << "...free variables now " << fvs << std::endl;
    Subs stmp;
    stmp.add(vc, gs);
    cur = stmp.apply(cur);
    stmp.applyToRange(subs);
    subs.add(vc, gs);
    // cur is now a candidate term
    addGeneralizationTerm(cur, v, i, fvs);
    grecs.emplace_back(cur);
    if (fvs.empty())
    {
      break;
    }
    // new index
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

void ConflictConjectureGenerator::findCompatible(
    const Node& g,
    const std::vector<Node>& fvs,
    const Node& vlhs,
    GenTrie* gt,
    ConflictConjectureGenerator::State state,
    size_t fvindex)
{
  if (state != State::SUBSET || fvindex == fvs.size())
  {
    for (const std::pair<Node, Node>& cg : gt->d_gens)
    {
      if (cg.second == vlhs)
      {
        if (state == State::SUBSET)
        {
          candidateConjecture(cg.first, g);
        }
        else
        {
          candidateConjecture(g, cg.first);
        }
      }
      else
      {
        Trace("ccgen-debug")
            << "- found term " << cg.first << " but not for lhs " << vlhs
            << " vs " << cg.second << std::endl;
      }
    }
  }
  Trace("ccgen-debug") << "  findCompatible " << fvindex << "/" << fvs.size()
                       << " state = " << static_cast<int>(state) << std::endl;
  Assert(state != State::UNKNOWN || fvindex < fvs.size());
  for (std::pair<const Node, GenTrie>& cg : gt->d_children)
  {
    if (fvindex < fvs.size() && cg.first == fvs[fvindex])
    {
      Assert(state != State::SUPERSET);
      State newState = fvindex + 1 == fvs.size() ? State::SUBSET : state;
      findCompatible(g, fvs, vlhs, &cg.second, newState, fvindex + 1);
    }
    else if (std::find(fvs.begin() + fvindex, fvs.end(), cg.first) != fvs.end())
    {
      // we skipped a variable
      if (state != State::SUBSET)
      {
        findCompatible(g, fvs, vlhs, &cg.second, State::SUPERSET, fvindex);
      }
    }
    else if (state != State::SUPERSET)
    {
      findCompatible(g, fvs, vlhs, &cg.second, State::SUBSET, fvindex);
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

void ConflictConjectureGenerator::candidateConjecture(const Node& ai,
                                                      const Node& bi)
{
  if (ai == bi)
  {
    return;
  }
  if (ai.isVar())
  {
    if (expr::hasSubterm(bi, ai))
    {
      // corner case of the form x = t[x], flip sides
      candidateConjecture(bi, ai);
    }
    // otherwise, definitely bogus
    return;
  }
  Node a = ai;
  Node b = bi;
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

bool ConflictConjectureGenerator::filterConjecture(const Node& clem)
{
  Trace("cconj-filter") << "Candidate conjecture : " << clem[0]
                        << " == " << clem[1] << "?" << std::endl;
  if (d_conjGenCache.find(clem) != d_conjGenCache.end())
  {
    Trace("cconj-filter") << "...already in cache" << std::endl;
    return true;
  }
  Node a = clem[0];
  Node b = clem[1];

  if (options().quantifiers.ccgenFilterEval)
  {  
    Trace("cconj-filter") << "Try filter based on evaluation" << std::endl;
    if (filterEvalsToFalse(a, b))
    {
      Trace("cconj-filter") << "...filtered based on evaluation" << std::endl;
      return true;
    }
  }
  
  Trace("cconj-filter") << "Try filter based on E-matching" << std::endl;
  if (filterEmatching(a, b))
  {
    Trace("cconj-filter") << "...filtered based on E-matching" << std::endl;
    return true;
  }

  Trace("cconj-filter") << "Try filter based on deductively entailed"
                        << std::endl;
  if (filterDeductivelyEntailed(a, b))
  {
    Trace("cconj-filter") << "...filtered based on deductively entailed"
                          << std::endl;
    return true;
  }
  
  return false;
}

bool ConflictConjectureGenerator::filterEmatching(const Node& a, const Node& b)
{
  if (!a.hasOperator())
  {
    // we don't expect this to happen, but in case it does we given an
    // assertion failure
    Assert(false);
    return false;
  }
  // TODO: cache E-matching for a, for checking a = b1 and a = b2
  Node op = a.getOperator();
  TermDb* tdb = getTermDatabase();
  EntailmentCheck* ec = d_treg.getEntailmentCheck();
  std::vector<Node> reps;
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
  size_t confirmed = 0;
  size_t tested = 0;
  for (const Node& r : reps)
  {
    Trace("cconj-filter-debug") << "- look in " << r << std::endl;
    Subs match;
    // filter based on E-matching and test
    std::vector<std::shared_ptr<EMatchFrame>> emf;
    emf.emplace_back(std::make_shared<EMatchFrame>(tdb, d_ee, a, r));
    size_t eindex = 1;
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
      eindex--;
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
  for (size_t i = 0; i < model->getNumAssertedQuantifiers(); i++)
  {
    Node phi = model->getAssertedQuantifier(i);
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
  Trace("cconj-filter") << "Check with subsolver" << std::endl;
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

  d_funDefEvaluator.clear();

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

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
