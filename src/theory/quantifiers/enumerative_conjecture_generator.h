#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__ENUMERATIVE_CONJECTURE_GENERATOR_H
#define CVC5__THEORY__QUANTIFIERS__ENUMERATIVE_CONJECTURE_GENERATOR_H

#include "smt/env_obj.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class EnumerativeConjectureGenerator : public QuantifiersModule
{
 public:
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
  /** Pointer to the current node manager. */
  NodeManager* d_nodeManager;
  /** The sort of the root non-terminal. */
  TypeNode d_rootType;
  /** The root non-terminal symbol. */
  Node d_rootNonTerminal;

  // Functions
  template <class T>
  static bool member(std::vector<T> vec, T val)
  {
    return std::find(vec.begin(), vec.end(), val) != vec.end();
  }

  template <class T>
  static bool hasKey(const std::unordered_map<TypeNode, T>& m,
                     const TypeNode& k)
  {
    return m.find(k) != m.end();
  }
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__ENUMERATIVE_CONJECTURE_GENERATOR_H */
