#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__ENUMERATIVE_CONJECTURE_GENERATOR_H
#define CVC5__THEORY__QUANTIFIERS__ENUMERATIVE_CONJECTURE_GENERATOR_H

#include "expr/sygus_term_enumerator.h"
#include "expr/term_canonize.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/quant_module.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class Index
{
 public:
  std::vector<Node> d_terms;
  std::unordered_map<Node, Index> d_variableToIndex;
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

typedef std::vector<std::priority_queue<Candidate>> CandidateIndex;

class EnumerativeConjectureGenerator : public QuantifiersModule
{
 public:
  template <class T>
  using Vector = std::vector<T>;

  template <class T>
  using Set = std::unordered_set<T>;

  template <class K, class V>
  using Map = std::unordered_map<K, V>;

  template <class T>
  using CIt = typename T::const_iterator;

  template <class T>
  using Ref = std::reference_wrapper<T>;

  template <class T>
  using Ptr = std::unique_ptr<T>;

  template <class T>
  using Ptr = std::unique_ptr<T>;

  template <class T>
  using PriorityQueue = std::priority_queue<T>;

  template <class T, class U>
  using Pair = std::pair<T, U>;

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
  Map<TypeNode, std::vector<Node>> d_typeToVariables;
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

  // Functions, non-static

  void checkHelper();

  /** Given an left-hand term looks up the index for "compatible" right-hand
   * terms.  It returns a mapping from possible sizes of RHS terms to RHS
   * terms.
   */
  std::vector<std::vector<Node>> oldFindCompatible(TNode lhs);

  // Functions, static

  static std::vector<std::vector<Node>> findCompatible(
      const size_t maximumSize,
      const size_t maximumDifference,
      const Map<Node, Index>& variableToIndex,
      expr::TermCanonize& termCanonize,
      const Map<TypeNode, std::uint8_t>& typeToNumber,
      TNode canonical);

  /** Returns a vector of substitutions such that the image of 'canonical' under
   * each substitution is a member of some known equivalence class. */
  static std::vector<Subs> findSubstitutions(
      TermDb* termDatabase,
      eq::EqualityEngine* equalityEngine,
      TNode canonical,
      const bool preferConstRepresentatives,
      const bool preferActiveTerms);

  template <class T>
  static bool member(std::vector<T> vec, T val)
  {
    return std::find(vec.begin(), vec.end(), val) != vec.end();
  }

  template <class T>
  static bool member(std::unordered_set<T> set, T val)
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

  static void addTerm(expr::TermCanonize& termCanonize,
                      const Map<TypeNode, std::uint8_t>& typeToNumber,
                      const Node term,
                      Map<Node, Index>& variableToIndex);

  static void debugPrintIndex(
      std::ostream& out,
      const std::unordered_map<Node, Index>& rootVariableToIndex);

  static void debugPrintSizeToCanonicals(
      std::ostream& out,
      const size_t maximumSize,
      const std::vector<std::unordered_set<Node>>& sizeToCanonicals);

  static void updateClock(const QEffort qEffort,
                          size_t& clock,
                          const size_t period);

  static std::vector<Node> getRelevantFunctionSymbols(TermDb* termDatabase);

  static void updateSymbolToKind(TermDb* termDatabase,
                                 const std::vector<Node>& functionSymbols,
                                 std::unordered_map<Node, Kind>& symbolToKind);

  static std::vector<TypeNode> getRelevantTypes(
      const std::vector<Node>& functionSymbols);

  static void updateTypeToIn(NodeManager* nodeManager,
                             const std::vector<TypeNode>& types,
                             const TypeNode rootType,
                             std::unordered_map<TypeNode, Node>& typeToIn);

  static void updateTypeToNonTerminal(
      const std::vector<TypeNode>& types,
      std::unordered_map<TypeNode, Node>& typeToNonTerminal);

  static void updateTypeToVariables(
      const std::vector<TypeNode>& types,
      expr::TermCanonize& termCanonize,
      const size_t maximumSize,
      std::unordered_map<TypeNode, std::vector<Node>>& typeToVariables);

  static std::vector<Node> getNonTerminals(
      const TNode rootNonTerminal,
      const std::vector<TypeNode>& types,
      const std::unordered_map<TypeNode, Node>& typeToNonTerminal);

  static TypeNode getGrammarType(
      NodeManager* nodeManagerPtr,
      const TNode rootNonTerminal,
      const std::vector<Node>& functionSymbols,
      const std::unordered_map<Node, Kind>& symbolToKind,
      const std::vector<TypeNode>& types,
      const std::unordered_map<TypeNode, Node>& typeToNonTerminal,
      const std::unordered_map<TypeNode, Node>& typeToIn,
      const std::unordered_map<TypeNode, std::vector<Node>>& typeToVariables);

  static std::vector<std::pair<Node, Node>> getInjectorRules(
      NodeManager* nodeManagerPtr,
      const TNode rootNonTerminal,
      const std::vector<TypeNode>& types,
      const std::unordered_map<TypeNode, Node>& typeToNonTerminal,
      const std::unordered_map<TypeNode, Node>& typeToIn);

  static std::vector<std::pair<Node, Node>> getFunctionRules(
      NodeManager* nodeManagerPtr,
      const std::vector<Node>& functionSymbols,
      const std::unordered_map<Node, Kind>& symbolToKind,
      const std::unordered_map<TypeNode, Node>& typeToNonTerminal);

  static std::vector<std::pair<Node, Node>> getVariableRules(
      const std::vector<TypeNode>& types,
      const std::unordered_map<TypeNode, Node>& typeToNonTerminals,
      const std::unordered_map<TypeNode, std::vector<Node>> typeToVariables);

  static std::pair<std::vector<std::unordered_set<Node>>,
                   std::unordered_map<Node, Index>>
  getEnumerationData(SygusTermEnumerator& termEnumerator,
                     expr::TermCanonize& termCanonize,
                     const Map<TypeNode, std::uint8_t>& typeToNumber,
                     const size_t maximumSize);

  static size_t computeSize(TNode n);

  static size_t underestimateSize(TNode n);

  static TypeNode findTypeByName(const std::string& name,
                                 const std::vector<TypeNode>& types);

  static Node findFunctionSymbolByName(const std::string& name,
                                       const std::vector<Node>& symbols);

  static void debugPrintLHSToSubstitutions(
      std::ostream& out,
      const Vector<Set<Node>>& sizeToCanonicals,
      const Map<Node, Vector<Subs>>& canonicalToSubstitutions);

  static std::unordered_map<Node, std::vector<Subs>>
  getCanonicalToSubstitutions(
      TermDb* termDatabase,
      eq::EqualityEngine* equalityEngine,
      const std::vector<std::unordered_set<Node>>& sizeToCanonicals,
      const bool preferConstRepresentatives,
      const bool preferActiveTerms);

  static CandidateIndex getCandidateIndex(
      const size_t maximumSize,
      const size_t maximumDifference,
      expr::TermCanonize& termCanonize,
      EntailmentCheck* entailmentCheck,
      eq::EqualityEngine* equalityEngine,
      const std::vector<std::unordered_set<Node>>& sizeToCanonicals,
      const std::unordered_map<Node, Index>& variableToIndex,
      const Map<TypeNode, std::uint8_t>& typeToNumber,
      const std::unordered_map<Node, std::vector<Subs>>&
          canonicalToSubstitutions);

  static std::pair<size_t, size_t> getScore(
      EntailmentCheck* entailmentCheck,
      const eq::EqualityEngine* equalityEngine,
      TNode canonical,
      TNode compatible,
      const std::vector<Subs>& substitutions);

  static Vector<Node> getSortedVariables(
      const expr::TermCanonize& termCanonize,
      const Map<TypeNode, std::uint8_t>& typeToNumber,
      TNode term);

  static bool variableLessThan(const expr::TermCanonize& termCanonize,
                               const Map<TypeNode, std::uint8_t>& typeToNumber,
                               TNode n0,
                               TNode n1);

  static void debugPrintSizeToCompatibles(
      std::ostream& out,
      TNode canonical,
      const Vector<Vector<Node>>& szToCompats);

  static bool isSymbolRelevant(const TermDb* termDb, const size_t i);

  static void debugPrintCandidateIndex(
      std::ostream& out, const Vector<PriorityQueue<Candidate>>& candIdx);

  static bool areSame(const Vector<Node>& v, const Vector<Node>& w);

  static void updateTypeToNumber(const Vector<TypeNode>& types,
                                 Map<TypeNode, std::uint8_t>& typeToNum);
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
