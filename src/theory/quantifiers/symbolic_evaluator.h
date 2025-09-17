#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYMBOLIC_EVALUATOR_H
#define CVC5__THEORY__QUANTIFIERS__SYMBOLIC_EVALUATOR_H

#include "smt/env_obj.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class SymbolicEvaluator : public QuantifiersModule
{
 public:
  SymbolicEvaluator(Env& env,
                    QuantifiersState& qs,
                    QuantifiersInferenceManager& qim,
                    QuantifiersRegistry& qr,
                    TermRegistry& tr);
  ~SymbolicEvaluator();
  bool needsCheck(Theory::Effort e) override;
  void reset_round(Theory::Effort e) override;
  void check(Theory::Effort e, QEffort quant_e) override;
  std::string identify() const override;
 private:
  void setUpEvaluator();
  void printPlusTerms();
  FunDefEvaluator d_evaluator;
  bool d_set_up_evaluator;
  size_t d_round;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY_QUANTIFIERS__SYMBOLIC_EVALUATOR_H */
