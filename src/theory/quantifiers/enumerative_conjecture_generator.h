#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__ENUMERATIVE_CONJECTURE_GENERATOR_H
#define CVC5__THEORY__QUANTIFIERS__ENUMERATIVE_CONJECTURE_GENERATOR_H

#include "expr/e_match.h"
#include "expr/sygus_term_enumerator.h"
#include "expr/term_canonize.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/quant_module.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/smt_engine_subsolver.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class Index
{
 public:
  std::vector<Node> d_terms;
  std::unordered_map<Node, Index*> d_variableToIndex;
};

class Candidate
{
 public:
  Node d_left;
  Node d_right;
  size_t d_tested;
  size_t d_confirmed;

  Candidate(TNode left,
            TNode right,
            const size_t tested,
            const size_t confirmed);
};

/**
 * There is a natural number 'n' such that, for each natural number 'i' less
 * than n, candidateIndex[i] is a priority queue of candidate conjectures where
 * the highest-priority candidate is at the top.  Candidate 'c1' is prioritized
 * over candidate 'c0' if -- but not only if -- c1.d_confirmed > c0.d_confirmed.
 */
typedef std::vector<std::priority_queue<Candidate>> CandidateIndex;

class EcgCandidateCallback : public CandidateCallback
{
 public:
  TermDb *d_termDatabase;
  bool d_preferActiveTerms;

  EcgCandidateCallback(
    TermDb *termDatabase,
    const bool preferActiveTerms) :
    CandidateCallback(),
    d_termDatabase(termDatabase),
    d_preferActiveTerms(preferActiveTerms)
  {}

  bool consider(TNode candidate) override
  {
    return
      (!d_preferActiveTerms ||
       d_termDatabase->isTermActive(candidate));
  }
};

class EnumerativeConjectureGenerator : public QuantifiersModule
{
 public:
  enum FilterResult
  {
    TRIVIAL,
    CACHED,
    DEDUCTIVE,
    INDUCTIVE,
    NONE
  };

  template <class T>
  using Vector = std::vector<T>;

  template <class T>
  using Set = std::unordered_set<T>;

  template <class K, class V>
  using Map = std::unordered_map<K, V>;

  template <class T>
  using It = typename T::iterator;

  template <class T>
  using CIt = typename T::const_iterator;

  template <class T>
  using Ref = std::reference_wrapper<T>;

  template <class T>
  using Ptr = std::unique_ptr<T>;

  template <class T>
  using PriorityQueue = std::priority_queue<T>;

  template <class T, class U>
  using Pair = std::pair<T, U>;

  template <class T>
  using Optional = std::optional<T>;

  typedef Pair<size_t, size_t> Score;

  // Functions
  EnumerativeConjectureGenerator(Env& env,
                                 QuantifiersState& qs,
                                 QuantifiersInferenceManager& qim,
                                 QuantifiersRegistry& qr,
                                 TermRegistry& tr);
  ~EnumerativeConjectureGenerator();
  bool needsCheck(Theory::Effort e) override;
  void reset_round(Theory::Effort e) override;
  void check(Theory::Effort e, QEffort quant_e) override;
  std::string identify() const override;

  // Fields
  /** The sort of the root non-terminal. */
  TypeNode d_rootType;
  /** The maximum size, "generalization depth", of an LHS/RHS term. */
  size_t d_maximumSize;
  /** See quantifiers_options.toml. */
  size_t d_maximumDifference;

 private:
  // Fields
  /** The collection of relevant function symbols.  We rebuild this each time
      `check()` is called. */
  Vector<Node> d_relevantFunctionSymbols;
  /** The collection of relevant types.  Each type is associated with a
      non-terminal in the grammar.  It is built from the domain and range types
      of the relevant function symbols. */
  Vector<TypeNode> d_relevantTypes;
  /** Mapping from types to numbers so that the types can be ordered. */
  Map<TypeNode, std::uint8_t> d_typeToNumber;
  /** Maps each relevant type to a function the type to the type of the root
   * non-terminal. */
  Map<TypeNode, Node> d_typeToIn;
  /** Maps each relevant type to a bound variable that represents its
   * non-terminal in the grammar. */
  Map<TypeNode, Node> d_typeToNonTerminal;
  /** Maps function and constructor symbols to the kinds of their applcations.
      Every function symbol is mapped to APPLY_UF and every constructor symbol
      is mapped to APPLY_CONSTRUCTOR. */
  Map<Node, Kind> d_symbolToKind;
  /** Maps each relevant type to a list of "free" variables of that type. */
  Map<TypeNode, Vector<Node>> d_typeToVariables;
  /** Maps each size from 0 to d_maximumSize to a set of canonical (LHS) terms.
   */
  Vector<Set<Node>> d_sizeToCanonicals;
  /** Maps each canonical variable to a trie of terms generated from the
   * grammar. */
  Map<Node, Index> d_variableToIndex;
  /** Conjectures that have been promoted to theorems because we were able to
   * prove them using induction. */
  Set<Node> d_inductivelyEntailed;
  /** Conjectures that have been promoted to theorems because we were able to
   * prove them without induction. */
  Set<Node> d_deductivelyEntailed;
  /**
   * The non-quantified formulas necessary for inductive entailment checks will
   * be stashed here.  These are exactly the fixed SAT literals in the theory
   * of uninterpreted functions that do not contain skolem variables.  They are
   * computed once, during the first call to this object's check() function,
   * and then cached away for the remainder of cvc5's execution.
   */
  Optional<Set<TNode>> d_initialFacts;
  /** Term canonization utility. */
  expr::TermCanonize d_termCanonize;
  /** Pointer to the current node manager. */
  NodeManager* d_nodeManager;
  /** The root non-terminal symbol. */
  Node d_rootNonTerminal;
  /** We only generate conjectures every d_period many calls to check() at
   * standard effort and we use d_clock to track this. */
  size_t d_clock;
  size_t d_period;
  bool d_preferConstRepresentatives;
  bool d_preferActiveTerms;
  bool d_subsolverEMatchFilter;
  Options d_defaultOptions;
  Set<TNode> d_conjectures;
  bool d_split;  

  /**
   * Use the variable below if ecgSubsolverEMatchFilter is true.  Initialize it
   * with the initial facts when you set d_initialFacts in check().  Ensure that
   * the following options are turned OFF:
   *
   * - quantInduction
   * - dtStcInduction
   * - conjectureGen
   * - enumerativeConjectureGenerator
   * - conflictBasedInst
   * - quantSubCbqi
   *
   * Ensure the following options are turned ON.
   *
   * - contextualEnumerator
   * - instMaxRounds with the value 10
   */
  std::unique_ptr<SolverEngine> d_filteringSubsolver;

  /**
   * Use the variable below to store a pointer to the e-matching callback.  The
   * managed object is ideally constructed once, during the first call to
   * check().  A pointer to the managed object is passed to
   * findSubstitutionsPreferred().  The purpose of the callback ought to be
   * clear from its implementation.
   */
  std::unique_ptr<EcgCandidateCallback> d_ecgCandidateCallback;

  // Functions, non-static

  void checkHelper();

  /** Given an left-hand term looks up the index for "compatible" right-hand
   * terms.  It returns a mapping from possible sizes of RHS terms to RHS
   * terms.
   */
  std::vector<std::vector<Node>> oldFindCompatible(TNode lhs);

  void debugPrintFacts(std::ostream& out, const Set<TNode>& facts);

  std::vector<std::vector<Node>> findCompatible(
      const size_t maximumSize,
      const size_t maximumDifference,
      const Map<Node, Index>& variableToIndex,
      expr::TermCanonize& termCanonize,
      const Map<TypeNode, std::uint8_t>& typeToNumber,
      TNode canonical);

  /**
   * The following function returns a vector of substitutions such that for each
   * substitution 'sigma' in the result the image of 'canonical' under 'sigma'
   * is represented in the equality engine.  When we say that the image is
   * represented in the equality engine we mean that it may not literally be in
   * the equality engine and the equalities stored in the equality engine entail
   * that the image is equivalent to a term that is in the equality engine.  See
   * _Definition 6_ in _Relational E-matching_ by Zhang et al. 2022.
   *
   * 'canonical' represents the left-hand side of some future candidate
   * conjecture but in this context we simply accept it as a pattern for
   * e-matching. I feel the remaining arguments do not warrant an explanation
   * right now.
   *
   * The following function is the _preferred_ implementation of
   * findSubstitutions because it uses the e-matching implementation from
   * ../../expr/e_match.cpp which is _more sound_ and _more complete_ than the
   * implementation in ./enumerative_conjecture_generator.cpp.  The former means
   * that I am more confident that for each substitution 'sigma' in the result
   * vector the term sigma.apply(canonical) is represented in equalityEngine.
   * The latter means that the e-matching implementation is also more likely to
   * discover such substitutions.  However the e-matching implementation is
   * still _incomplete_.  It is not guaranteed to find all substitutions 'sigma'
   * such that sigma.apply(canonical) is represented in equalityEngine.
   */
  std::vector<Subs> findSubstitutionsPreferred(
    TermDb *termDatabase,
    eq::EqualityEngine *equalityEngine,
    TNode canonical,
    const bool preferConstRepresentatives,
    const bool preferActiveTerms,
    const std::int64_t substitutionLimit);

  /** Returns a vector of substitutions such that the image of 'canonical' under
   * each substitution is a member of some known equivalence class. */
  std::vector<Subs> findSubstitutions(
      TermDb* termDatabase,
      eq::EqualityEngine* equalityEngine,
      TNode canonical,
      const bool preferConstRepresentatives,
      const bool preferActiveTerms,
      const std::int64_t substitutionLimit);

  template <class T>
  static bool member(const std::vector<T>& vec, T val)
  {
    return std::find(vec.begin(), vec.end(), val) != vec.end();
  }

  template <class T>
  static bool member(std::vector<T>& vec, T val)
  {
    return std::find(vec.begin(), vec.end(), val) != vec.end();
  }

  template <class T>
  static bool member(const std::unordered_set<T>& set, T val)
  {
    return set.find(val) != set.end();
  }

  template <class T>
  static bool member(std::unordered_set<T>& set, T val)
  {
    return set.find(val) != set.end();
  }

  template <class T, bool persistent>
  static bool hasKey(const std::unordered_map<NodeTemplate<persistent>, T>& m,
                     const NodeTemplate<persistent>& k)
  {
    return m.find(k) != m.end();
  }

  template <class T>
  static bool hasKey(const std::unordered_map<TypeNode, T>& m,
                     const TypeNode& k)
  {
    return m.find(k) != m.end();
  }

  template <class T>
  static bool hasKey(const std::unordered_map<Node, T>& m, const Node& k)
  {
    return m.find(k) != m.end();
  }

  /**
   * This is an important note about the implementation of addTerm.  Observe
   * that rootVariableToIndex is an instance of Map<Node, Index> while on the
   * other hand the d_variableToIndex field in the Index class is an instance of
   * Map<Node, Index*>.  This means that for any 'v' that is an instance of
   * Node, rootVariableToIndex[v] is a safe operation in the sense that if
   * rootVariableToIndex does not associate v with an Index then one will be
   * created automatically.  However suppose 'index' represents a pointer to
   * rootVariableToIndex[v].  index->d_variableToIndex[v] is an unsafe
   * operation.  It will likely cause a segfault if d_variableToIndex does not
   * already associate v with an Index*.  This is why we set
   * index->d_variableToIndex[v] to 'new Index()' if index->d_variableToIndex
   * does not have v as a key already.
   */
  void addTerm(expr::TermCanonize& termCanonize,
                      const Map<TypeNode, std::uint8_t>& typeToNumber,
                      const Node term,
                      Map<Node, Index>& rootVariableToIndex);

  void debugPrintIndex(
      std::ostream& out,
      const std::unordered_map<Node, Index>& rootVariableToIndex);

  void debugPrintSizeToCanonicals(
      std::ostream& out,
      const size_t maximumSize,
      const std::vector<std::unordered_set<Node>>& sizeToCanonicals);

  void updateClock(size_t& clock, const size_t period);

  std::vector<Node> getRelevantFunctionSymbols(TermDb* termDatabase);

  void updateSymbolToKind(TermDb* termDatabase,
                                 const std::vector<Node>& functionSymbols,
                                 std::unordered_map<Node, Kind>& symbolToKind);

   std::vector<TypeNode> getRelevantTypes(
      const std::vector<Node>& functionSymbols);

   void updateTypeToIn(NodeManager* nodeManager,
                             const std::vector<TypeNode>& types,
                             const TypeNode rootType,
                             std::unordered_map<TypeNode, Node>& typeToIn);

   void updateTypeToNonTerminal(
      const std::vector<TypeNode>& types,
      std::unordered_map<TypeNode, Node>& typeToNonTerminal);

   void updateTypeToVariables(
      const std::vector<TypeNode>& types,
      expr::TermCanonize& termCanonize,
      const size_t maximumSize,
      const size_t varsPerType,
      std::unordered_map<TypeNode, std::vector<Node>>& typeToVariables);

   std::vector<Node> getNonTerminals(
      const TNode rootNonTerminal,
      const std::vector<TypeNode>& types,
      const std::unordered_map<TypeNode, Node>& typeToNonTerminal);

   TypeNode getGrammarType(
      NodeManager* nodeManagerPtr,
      const TNode rootNonTerminal,
      const std::vector<Node>& functionSymbols,
      const std::unordered_map<Node, Kind>& symbolToKind,
      const std::vector<TypeNode>& types,
      const std::unordered_map<TypeNode, Node>& typeToNonTerminal,
      const std::unordered_map<TypeNode, Node>& typeToIn,
      const std::unordered_map<TypeNode, std::vector<Node>>& typeToVariables);

   std::vector<std::pair<Node, Node>> getInjectorRules(
      NodeManager* nodeManagerPtr,
      const TNode rootNonTerminal,
      const std::vector<TypeNode>& types,
      const std::unordered_map<TypeNode, Node>& typeToNonTerminal,
      const std::unordered_map<TypeNode, Node>& typeToIn);

   std::vector<std::pair<Node, Node>> getFunctionRules(
      NodeManager* nodeManagerPtr,
      const std::vector<Node>& functionSymbols,
      const std::unordered_map<Node, Kind>& symbolToKind,
      const std::unordered_map<TypeNode, Node>& typeToNonTerminal);

   std::vector<std::pair<Node, Node>> getVariableRules(
      const std::vector<TypeNode>& types,
      const std::unordered_map<TypeNode, Node>& typeToNonTerminals,
      const std::unordered_map<TypeNode, std::vector<Node>> typeToVariables);

   std::pair<std::vector<std::unordered_set<Node>>,
                   std::unordered_map<Node, Index>>
  getEnumerationData(SygusTermEnumerator& termEnumerator,
                     expr::TermCanonize& termCanonize,
                     const Map<TypeNode, std::uint8_t>& typeToNumber,
                     const size_t maximumSize);

   size_t computeSize(TNode n);

   size_t underestimateSize(TNode n);

   TypeNode findTypeByName(const std::string& name,
                                 const std::vector<TypeNode>& types);

   Node findFunctionSymbolByName(const std::string& name,
                                       const std::vector<Node>& symbols);

   void debugPrintLHSToSubstitutions(
      std::ostream& out,
      const Vector<Set<Node>>& sizeToCanonicals,
      const Map<Node, Vector<Subs>>& canonicalToSubstitutions);

   /**
    * If the quantifiers option 'ecgSubsolverEMatchFilter' is _false_ then this
    * function maps each LHS pattern in 'sizeToCanonicals' to its image under
    * 'findSubstitutionsPreferred'.  If the same option is true then this
    * function returns an empty map because the subsolver will compute the
    * substitutions instead of the main solver.
    *
    * Let us return to the first sentence in the above paragraph.  Recall that
    * for each canonical (term) in sizeToCanonicals the term's head symbol is an
    * injector, a function symbol that carries the actual LHS pattern into the
    * type of the grammar's root non-terminal symbol.  We remove the injector
    * from each term before associating it with a collection of substitutions in
    * getCanonicalToSubstitutions.  To say it once again: none of the keys in
    * getCanonicalToSubstitutions mentions an injector.
    */
   std::unordered_map<Node, std::vector<Subs>>
  getCanonicalToSubstitutions(
      TermDb* termDatabase,
      eq::EqualityEngine* equalityEngine,
      const std::vector<std::unordered_set<Node>>& sizeToCanonicals,
      const bool preferConstRepresentatives,
      const bool preferActiveTerms,
      const std::int64_t substitutionLimit);

   /** 
    * Implementation note 1: The terms in szToCanons all have an injector
    * function symbol as their head function symbol.  In constrast to this none
    * of the keys in lhsToSubss mention an injector function symbol.  This means
    * that if 't' is a term from szToCanons then the substitutions under which t
    * is represented in the equality engine can be obtained with
    * lhsToSubss.at(t[0]).
    *
    * Implementation note 2: This function should behave differently depending
    * on the value of d_subsolverEMatchFilter.  If d_subsolverEMatchFilter is
    * true then we expect the dictionary lhsToSubss to be _empty_ since we will
    * rely on d_filteringSubsolver to compute substitutions.  On the other hand
    * if d_subsolverEmatchFilter is false then we expect that
    * lhsToSubss.at(t[0]) will succeed for any term 't' from szToCanons.  To
    * reiterate we expect that all calls to 'at()' can be unguarded when
    * d_subsolverEMatchFilter is _false_.
    */
   CandidateIndex getCandidateIndex(
      const size_t maximumSize,
      const size_t maximumDifference,
      expr::TermCanonize& termCanonize,
      EntailmentCheck* entailmentCheck,
      eq::EqualityEngine* equalityEngine,
      const Vector<Set<Node>>& szToCanons,
      const Map<Node, Index>& variableToIndex,
      const Map<TypeNode, std::uint8_t>& typeToNumber,
      const Map<Node, Vector<Subs>>& lhsToSubss,
      NodeManager* nodeMgr,
      const Set<Node>& dedEnt,
      const Set<Node>& indEnt);

   /**
    * We take the following steps to assign a score to 'conjecture'.  Remember
    * that a score is a pair whose first component is _nominally_ the number of
    * substitutions tested and whose second component is the number of
    * substitutions under which the LHS and RHS are entailed to be equivalent.
    * We iterate over all the substitutions in 'subss', which are all grounding
    * substitutions.  For each substitution 'sigma' we apply sigma to the LHS
    * and RHS of the conjecture.  We then handle 5 possibilities.
    *
    * 1. Either one of sigma(LHS) or sigma(RHS) is not represented in the
    * congruence closure (as determined by an incomplete procedure).  In this
    * case we do not bump 'tested' or 'confirmed'.
    *
    * 2. sigma(LHS) and sigma(RHS) are represented in the congruence closure and
    * live in the same equivalence class.  Here we bump both tested and
    * confirmed.
    *
    * 3. sigma(LHS) and sigma(RHS) are represented in the c.c., live in
    * different equivalence classes, and both equivalence class representatives
    * are ground constructor terms.  If we trust the current partial model for
    * our recursive functions then sigma(LHS) and sigma(RHS) cannot possibly be
    * equivalent.  We bump tested but do not bump confirmed.  Any conjecture
    * where confirmed < tested will be discarded later.
    *
    * 4. sigma(LHS) and sigma(RHS) are represented in the c.c., live in
    * different equivalence classes, the representatives are not ground
    * constructor terms, but the solver says they are forced to be disequal.  We
    * handle this case the same as case #3.  5. Otherwise we leave both tested
    * and confirmed unchanged.
    */
   std::pair<size_t, size_t> getScoreMainSolver(
     TNode conjecture,
     const Vector<Subs>& subss,
     EntailmentCheck* entChk,
     const eq::EqualityEngine* ee);

   std::pair<size_t, size_t> getScoreSubsolver(
     Node conjecture,
     SolverEngine *filteringSubsolver);

   std::pair<size_t, size_t> getScore(
      EntailmentCheck* entailmentCheck,
      const eq::EqualityEngine* equalityEngine,
      TNode canonical,
      TNode compatible,
      const Vector<Subs>& substitutions,
      NodeManager* nodeMgr,
      const Set<Node>& dedEnt,
      const Set<Node>& indEnt);

   Vector<Node> getSortedVariables(
      const expr::TermCanonize& termCanonize,
      const Map<TypeNode, std::uint8_t>& typeToNumber,
      TNode term);

   bool variableLessThan(const expr::TermCanonize& termCanonize,
                               const Map<TypeNode, std::uint8_t>& typeToNumber,
                               TNode n0,
                               TNode n1);

   void debugPrintSizeToCompatibles(
      std::ostream& out,
      TNode canonical,
      const Vector<Vector<Node>>& szToCompats);

   bool isSymbolRelevant(const TermDb* termDb, const size_t i);

   void debugPrintCandidateIndex(
      std::ostream& out, const Vector<PriorityQueue<Candidate>>& candIdx);

   bool areSame(const Vector<Node>& v, const Vector<Node>& w);

   void updateTypeToNumber(const Vector<TypeNode>& types,
                                 Map<TypeNode, std::uint8_t>& typeToNum);

   void filterCandidates(
      Env& env,
      Options& subsolverOpts,
      quantifiers::QuantifiersInferenceManager& quantInfMgr,
      quantifiers::TermRegistry& termReg,
      NodeManager* nodeMgr,
      const std::int64_t initialFuel,
      Set<Node>& indEnt,
      Set<Node>& dedEnt,
      const size_t timeout,
      const Set<TNode>& initialFacts,
      Vector<PriorityQueue<Candidate>>& candIdx,
      Set<TNode>& conjectures,
      const quantifiers::QuantifiersState& quantifiersState,
      const bool split);

   bool filterConjecture(Env& env,
                               Options& subsolverOpts,
                               quantifiers::TermRegistry& termReg,
                               Set<Node>& indEnt,
                               Set<Node>& dedEnt,
                               Vector<Node>& indEntBuf,
                               Optional<std::int64_t>& fuel,
                               const size_t timeout,
                               const Set<TNode>& initialFacts,
                               TNode conj,
                               const Set<TNode>& conjectures,
                               const TNode trueNode,
                               const quantifiers::QuantifiersState& quantifiersState,
                               const bool split);

   void assertConjecture(
      quantifiers::QuantifiersInferenceManager& quantInfMgr, TNode conj, const bool split, const Vector<Node>& indEntBuf);

   Node candidateToConjecture(NodeManager* nodeMgr,
                                    const Candidate& cand,
                                    theory::Rewriter* rewriter);

   bool isEntailed(Env& env,
                         Options& subsolverOpts,
                         quantifiers::TermRegistry& termReg,
                         const Vector<Node>& extra,
                         const bool induct,
                         const size_t timeout,
                         const Set<TNode>& initialFacts,
                         TNode conj);

   void debugPrintAssertions(std::ostream& out,
                                   const Vector<Node>& assertions);

   void debugPrintFilterConjecture(std::ostream& out, TNode conj, FilterResult result);

   Set<TNode> getProvedConjectures(const Set<TNode>& conjectures, const Valuation& valuation, const quantifiers::TermRegistry& termReg);

   /**
    * Observe that there are two different member functions with the name
    * getInitialFacts.  The older function uses a valuation and a term registry
    * to retrieve all assertions, both quantified and quantifier-free, that are
    * fixed (i.e. decision level zero) SAT literals.  It is the *dispreferred*
    * implementation of getInitialFacts.  The newer implementation simply
    * accepts a vector of assertions.  We mean to feed it the vector of all
    * preprocessed assertions from the input file.  In some sense the newer
    * implementation is preferred because it is a more faithful reflection of
    * the initial assertions.
    */
   Set<TNode> getInitialFacts(const Vector<Node>& assertions);
   Set<TNode> getInitialFacts(Valuation& valuation, quantifiers::TermRegistry& termReg);
};

class Decision;

typedef std::vector<Decision*> Trail;

class Decision
{
 private:
  Node d_pattern;
  std::vector<Node> d_candidates;
  size_t d_nextCandidatePosition;
  std::vector<size_t> d_nonvariablePatternPositions;
  std::vector<size_t> d_variablePositions;
  std::unordered_set<size_t> d_boundPositions;
  bool d_preferConstRepresentatives;
  bool d_preferActiveTerms;

 public:
  Node getPattern();
  Decision(TermDb* termDatabase,
           eq::EqualityEngine* equalityEngine,
           TNode pattern,
           TNode representative,
           bool preferConstRepresentatives,
           bool preferActiveTerms);
  bool push(TermDb* termDatabase,
            eq::EqualityEngine* equalityEngine,
            Subs& substitution,
            Trail& trail);
  void pop(Subs& substitution);
  bool isFinished();
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__ENUMERATIVE_CONJECTURE_GENERATOR_H */
