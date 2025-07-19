/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CONFLICT_CONJECTURE_GENERATOR_H
#define CVC5__THEORY__QUANTIFIERS__CONFLICT_CONJECTURE_GENERATOR_H

#include "expr/term_canonize.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 */
class ConflictConjectureGenerator : public QuantifiersModule
{
 public:
  ConflictConjectureGenerator(Env& env,
                              QuantifiersState& qs,
                              QuantifiersInferenceManager& qim,
                              QuantifiersRegistry& qr,
                              TermRegistry& tr);
  ~ConflictConjectureGenerator() {}

  /** Presolve */
  void presolve() override;

  /** Needs check. */
  bool needsCheck(Theory::Effort e) override;

  /** Needs model. */
  QEffort needsModel(Theory::Effort e) override;

  /** Reset round. */
  void reset_round(Theory::Effort e) override;

  /** Register quantified formula q */
  void registerQuantifier(Node q) override;

  /** Check ownership for q */
  void checkOwnership(Node q) override;

  /** Check.
   * Adds instantiations for all currently asserted
   * quantified formulas via calls to process(...)
   *
   * check()
   *   | calls
   *   v                 _______________________________________
   * checkDisequality() | Derive conjectures from disequalities |
   *   |                '---------------------------------------'
   *   |                          ___________________________
   *   |--> getGeneralizations() | Add new terms to the trie |
   *   |             |           '---------------------------'
   *   |             |
   *   |             |-------------------------,   ____________________________________
   *   |             |                         |  | Add a single expansion to the trie |
   *   |             v                         v  '------------------------------------'
   *   |    getGeneralizationsInternal() --> addGeneralizationTerm()
   *   |             |
   *   |             v      __________________________________________
   *   |    getGenForEqc() | Iterate over terms in a particular       |
   *   |                   | equivalence class to discover expansions |
   *   |                   '------------------------------------------'
   *   v               ________________________________________________
   * findCompatible() | Search the trie for "compatible" LHS-RHS pairs |
   *   |              '------------------------------------------------'
   *   v                    __________________________________________
   * candidateConjecture() | Filter compatible LHS-RHS pairs based on |
   *                       | * e-matching                             |
   *                       | * canonicity                             |
   *                       '------------------------------------------'
   */
  void check(Theory::Effort e, QEffort quant_e) override;

  /** Identify. */
  std::string identify() const override;

 private:
  /** Cached value of nodeManager()->mkConst(false). */
  Node d_false;

  /** Cached value of Node::null(). */
  Node d_null;

  /** The equality engine of quantifiers. */
  eq::EqualityEngine* d_ee;

  /**
   * Used for evaluating recusively defined functions on variable-free terms.
   * Helps find counterexamples to candidate conjectures.
   */
  FunDefEvaluator d_funDefEvaluator;

  /**
   * Will help us recognize conjectures that are equivalent up to renaming of
   * bound variables by rewriting them in a canonical form.
   */
  expr::TermCanonize d_tc;

  /**
   * Maps a subset of the current equivalence class representatives -- those
   * that may be useful for conjecture generation -- to variables.  Since we're
   * going to be working with variables in the image of d_bv a lot, let's call
   * such variables 'equivalence class variables'.  All equivalence class
   * variables are expected to have the kind Kind::BOUND_VARIABLE.  We also
   * expect d_bv to be injective which ensures that it is invertible.
   */
  std::map<Node, Node> d_bv;

  /**
   * Inverse map of above.  To be clear: for any equivalence class
   * representative r in the domain of d_bv above we expect the following.
   *
   * d_bvToEqc[d_bv[r]] == r.
   */
  std::map<Node, Node> d_bvToEqc;

  /**
   * For each equivalence class variable v, d_eqcGen[v] will store v's immediate
   * expansions.  This is the set of v's immediate expansions:
   *
   * { f(d_bv[e_1],...,d_bv[e_n]) | f(e_1,...,e_n) is in the equivalence class
   * of d_bvToEqc[v], f is a user declared function symbol or a constructor
   * symbol, n >= 0, and each e_i is an equivalence class representative }
   */
  std::map<Node, std::vector<Node>> d_eqcGen;

  /**
   * For each equivalence class variable v, d_eqcGenRec[v] will store all the
   * *known* expansions of v.  Computing all expansions of v up front may be a
   * waste of time and space.  As we search for new conjectures we will discover
   * new expansions of v and record them in this map.
   *
   * So far we haven't defined what it means for a term s' to be an expansion of
   * a term s.  Suppose s' and s are both built using user defined function
   * symbols, constructor symbols, and equivalence class variables.  s' is an
   * expansion of s if there exists an equivalence class variable x and a term t
   * that satisfy all three conditions (1) x occurs in s, (2) t is an expansion
   * of x, and (3) s' = s[t/x].  Note that this is a recursive definition and
   * the 'base case' is where s is itself an equivalence class variable and s'
   * is one of its immediate expansions.
   */
  std::map<Node, std::vector<Node>> d_eqcGenRec;

  /**
   * The domain of this map is expected to be all the terms in the image of
   * d_eqcGenRec.  d_genToFv maps each known expansion to the collection of
   * equivalence class variables that occur in it.
   */
  std::map<Node, std::vector<Node>> d_genToFv;

  /**
   * This vector contains all the conjectures for which we have added splitting
   * lemmas.  Any conjecture in here has passed all our filters.
   */
  std::vector<Node> d_currConjectures;

  class GenTrie
  {
   public:
    /**
     * We know that the function getGeneralizationsInternal() accepts an
     * equivalence class variable and computes a number of its expansions.  Let
     * x be some equivalence class variable, let t be an expansion of x
     * discovered by getGeneralizationsInternal(), and let fvs be some
     * arrangement of the equivalence class variables of t (the exact
     * arrangement depends on how t was derived from x).  Since fvs is a
     * sequence of variables let's write it as v_1, ..., v_n where n >= 0.  The
     * function addGeneralizationTerm() accepts t, x, and fvs and inserts the
     * pair (t, x) into d_gtrie such that
     *
     * d_gtrie.d_children[v_1].(...).d_children[v_n].d_gens is guaranteed to
     * contain the pair (t, x) 
     *
     * Observe that fvs is the 'path' to (t, x) in d_gtrie.  In order to
     * remember this path, addGeneralizationTerm() maps t to fvs in d_genToFv.
     */
    std::map<Node, GenTrie> d_children;
    std::vector<std::pair<Node, Node>> d_gens;

    /**
     * Clear the index of expansions.
     */
    void clear();
  };

  /**
   * The index of all expansions discovered so far.  We expect that every
   * expansion recorded in d_eqcGenRec is also added to this index.
   */
  GenTrie d_gtrie;

  /**
   * d_conjBuffer.  This is cleared at the start of each call to
   * checkDisequality() and stores conjecture candidates for a particular
   * disequality before filtering.
   *
   * d_conjGen & d_conjGenIndex.  Any candidate conjecture that passes all filters is
   * added to this vector.  It is not cleared between instantiation rounds.  The next
   * conjecture to potentially make into a splitting lemma is d_conjGenIndex.get().
   * 
   * d_conjGenCache.  d_conjGenCache is a version of d_conjGen that is faster to
   * search through because it's a hash set as opposed to a vector.
   * 
   * d_currConjectures.  Once a conjecture from d_conjGen is sent as a splitting
   * lemma it is added to this vector.
   */
  context::CDList<Node> d_conjGen;
  context::CDO<size_t> d_conjGenIndex;
  /** The canonized version of lemmas in d_conjGen. */
  context::CDHashSet<Node> d_conjGenCache;
  std::unordered_set<Node> d_conjBuffer;

  /** The options for subsolver calls. */
  Options d_subOptions;

  /**
   * The function that inspects the context to build a grammar for conjecture
   * generation.
   */
  void buildGrammarFromContext();

  /**
   * Returns the equivalence class variable corresponding to the equivalence
   * class e.  Creates one if it doesn't exist then updates d_bv and d_bvToEqc.
   */
  Node getOrMkVarForEqc(const Node& e);

  /**
   * Populates d_eqcGen.
   */
  const std::vector<Node>& getGenForEqc(const Node& e);

  /**
   * Given a disequality (an equality currently in the equivalence class of false) it 
   */
  void checkDisequality(const Node& eq);

  /**
   * Calls getGeneralizationsInternal() a options().quantifiers.ccgenExpandReps
   * number of times.
   */
  void getGeneralizations(const Node& e);

  /**
   * See the note in the body of getGeneralizationsInternal() in
   * conflict_conjecture_generator.cpp.
   */
  void getGeneralizationsInternal(const Node& e);

  /**
   * See the note in the declaration of the GenTrie class.
   */
  void addGeneralizationTerm(const Node& g,
                             const Node& v,
                             size_t depth,
                             const std::vector<Node>& fvs);

  enum class State
  {
    UNKNOWN,
    SUPERSET,
    SUBSET
  };

  void findCompatible(const Node& g,
                      const std::vector<Node>& fvs,
                      const Node& vlhs,
                      GenTrie* gt,
                      State state,
                      size_t fvindex);

  /**
   * Called when FV(a) is a superset of FV(b).
   */
  void candidateConjecture(const Node& a, const Node& b);

  /**
   * Runs the candidate conjecture clem through all the filters. 
   */
  bool filterConjecture(const Node& clem);

  /**
   * See if there is a substituion sigma such that (a = b)*sigma is false, where
   * sigma maps to constants. Called when FV(a) is a superset of FV(b).
   *
   * @return true if we filter the conjecture a = b.
   */
  bool filterEmatching(const Node& a, const Node& b);

  /**
   * Calls a subsolver to check whether the proposed conjecture is a deductive
   * consequence of lemmas that have already been proved.  No induction or
   * conjecture generation is employed.
   */
  bool filterDeductivelyEntailed(const Node& a, const Node& b);

  /**
   * Currently unused.  I am keeping the code around for reference on how to use
   * the FunDefEvaluator.
   */
  void runFunDefEvaluatorExperiment();

  /**
   * Reconstructs recursive function definitions from their clauses provided as
   * separate assertions.  After constructing the definitions, feeds them to
   * d_funDefEvaluator.
   */
  void setUpFunDefEvaluator();

  /**
   * For each recursive datatype defines a SyGuS grammar to generate concrete
   * terms.  Generates a predefined number of concrete terms and then evaluates
   * a candidate conjecture on these terms to see if the left and right hand
   * terms actually evaluate to the same variable-free term.
   */
  bool filterEvalsToFalse(const Node& lhs, const Node& rhs);

  /** I'll document this after I finish writing it. */
  const std::unordered_set<Node> collectRecursivelyDefinedFunctionSymbols(quantifiers::FirstOrderModel* mdl);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
