#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CONTEXTUAL_ENUMERATOR_H
#define CVC5__THEORY__QUANTIFIERS__CONTEXTUAL_ENUMERATOR_H

#include "expr/sygus_grammar.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class ContextualEnumerator : public QuantifiersModule
{
  /*==========
   | Private |
   ==========*/
 private:
  /*************
   * Variables *
   *************/

  /**
   * Maps each type to its enumeration predicate.
   */
  std::unordered_map<TypeNode, Node> d_typeToPredicate;

  /**
   * The vector of function-like symbols for which we have already added
   * enumeration lemmas.
   */
  std::unordered_set<TNode> d_enumerated;

  /********************
   * Static functions *
   ********************/

  /**
   * Returns a vector whose elements are the relevant function symbols.
   * A symbol 'f' is relevant only if all these conditions are
   * met:
   *
   * 1. f is not a selector symbol,
   * 2. f is not a tester symbol,
   * 3. if f is an uninterpreted function symbol then:
   *     i. f is not a skolem, and
   *     ii. f does not have the CtxtEnumAttribute,
   * 4. the term database has a ground term that is an f-application,
   * 5. the first such ground term is active, (optional)
   * 6. that first term is also an atomic trigger (also optional).
   *
   * Any f that makes it through could be an uninterpreted function symbol,
   * a constructor symbol, a theory symbol, or something else.
   *
   * This function returns a vector<TNode> and not a vector<Node> because the
   * relevant function symbols and constructor symbols are owned by the term
   * database.
   */
  static std::vector<TNode> getRelevantFunctionSymbols(TermDb* tdb);

  static bool isSymbolRelevant(TNode f, TNode t, TermDb* tdb);

  static void debugPrintGrammar(const SygusGrammar& grammar, std::ostream& out);

  /************************
   * Non-static functions *
   ************************/

  std::vector<Node> collectSignatureInformation();
  void enumerateUf(const std::vector<Node>& enum_queue);
  std::vector<Node> enumerateTermsWithSygus(TNode term);
  bool isHandledTerm(const TNode n);
  Node getPredicateForType(TypeNode tn);
  void debugPrintEnumQueue(const std::vector<Node>& enum_queue);
  Node makeRootRule(
      const TNode f,
      const std::unordered_map<TypeNode, TNode>& typeToNonTerminal);
  void addConstantRules(SygusGrammar& sg);

  /*=========
   | Public |
   =========*/
 public:
  ContextualEnumerator(Env& env,
                       QuantifiersState& qs,
                       QuantifiersInferenceManager& qim,
                       QuantifiersRegistry& qr,
                       TermRegistry& tr);
  ~ContextualEnumerator();
  bool needsCheck(Theory::Effort e) override;
  void reset_round(Theory::Effort e) override;
  void check(Theory::Effort e, QEffort quant_e) override;
  std::string identify() const override;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__CONTEXTUAL_ENUMERATOR_H */
