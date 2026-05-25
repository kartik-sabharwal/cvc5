#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__ENUMERATIVE_CONJECTURE_GENERATOR_H
#define CVC5__THEORY__QUANTIFIERS__ENUMERATIVE_CONJECTURE_GENERATOR_H

#include "smt/env_obj.h"
#include "theory/quantifiers/quant_module.h"
#include "expr/sygus_term_enumerator.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "expr/term_canonize.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class Index;

class EnumerativeConjectureGenerator : public QuantifiersModule
{
 public:
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
  size_t computeSize(TNode n);
  size_t underestimateSize(TNode n);

  // Fields
  /** The sort of the root non-terminal. */
  TypeNode d_rootType;
  /** The map from canonical variables to LHS/RHS terms. */
  std::map<Node, Index> d_variableToIndex;
  /** The maximum size, "generalization depth", of an LHS/RHS term. */
  size_t d_maximumSize;

 private:
  // Fields
  /** The collection of relevant function symbols.  We rebuild this each time
      `check()` is called. */
  std::vector<TNode> d_rlvFuncSyms;
  /** The collection of relevant types.  Each type is associated with a
      non-terminal in the grammar.  It is built from the domain and range types
      of the relevant function symbols. */
  std::vector<TypeNode> d_rlvTypes;
  /** Maps each relevant type to a function the type to the type of the root
   * non-terminal. */
  std::unordered_map<TypeNode, Node> d_typeToIn;
  /** Maps each relevant type to a bound variable that represents its
      non-terminal in the grammar. */
  std::unordered_map<TypeNode, Node> d_typeToNonTerminal;
  /** Maps function and constructor symbols to the kinds of their applcations.
      Every function symbol is mapped to APPLY_UF and every constructor symbol
      is mapped to APPLY_CONSTRUCTOR. */
  std::unordered_map<TNode, Kind> d_symbolToKind;
  /** Maps each relevant type to a list of "free" variables of that type. */
  std::unordered_map<TypeNode, std::vector<Node>> d_typeToVariables;
  /** Term canonization utility. */
  expr::TermCanonize d_termCanonize;

  /** Pointer to the current node manager. */
  NodeManager* d_nodeManager;
  /** The root non-terminal symbol. */
  Node d_rootNonTerminal;

  // Functions
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

  template <class T>
  static bool hasKey(const std::unordered_map<TypeNode, T>& m,
                     const TypeNode& k)
  {
    return m.find(k) != m.end();
  }

  template <class T>
  static bool hasKey(const std::map<Node, T>& m, const Node& k)
  {
    return m.find(k) != m.end();
  }

  void addTerm(Node term, std::unordered_set<Node>& boundVariableSet);

  void debugPrintIndex(std::ostream& out);

  std::vector<Node> findCompatible(TNode lhs);
};

class EnumerativeConjectureGeneratorCallback : public SygusTermEnumeratorCallback
{
 bool addTerm(const Node& n, std::unordered_set<Node>& bterms) override;

 private:
  EnumerativeConjectureGenerator* d_enumerativeConjectureGenerator;
  size_t d_maximumSize;

 public:
  EnumerativeConjectureGeneratorCallback(EnumerativeConjectureGenerator* enumerativeConjectureGenerator, size_t maximumSize);
};

class Index
{
 public:
  std::vector<Node> d_terms;
  std::map<Node, Index> d_variableToIndex;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__ENUMERATIVE_CONJECTURE_GENERATOR_H */
