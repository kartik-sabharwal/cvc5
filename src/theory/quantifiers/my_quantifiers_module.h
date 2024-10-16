#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__MY_QUANTIFIERS_MODULE_H
#define CVC5__THEORY__QUANTIFIERS__MY_QUANTIFIERS_MODULE_H

#include "smt/env_obj.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class MyQuantifiersModule : public QuantifiersModule 
{
 public:
  MyQuantifiersModule(Env& env, QuantifiersState& qs,
    QuantifiersInferenceManager& qim, QuantifiersRegistry& qr,
    TermRegistry& tr) {};

  ~MyQuantifiersModule() {};

  bool needsCheck(Theory::Effort e) override {};

  void reset_round(Theory::Effort e) override {};

  void check(Theory::Effort e, QEffort quant_e) override {};

  std::string identify() const override {};
};

} // namespace quantifiers
} // namespace theory
} // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__MY_QUANTIFIERS_MODULE_H */
