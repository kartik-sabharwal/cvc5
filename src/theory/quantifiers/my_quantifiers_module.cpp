#include "theory/quantifiers/my_quantifiers_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

MyQuantifiersModule::MyQuantifiersModule(Env& env, QuantifiersState& qs,
  QuantifiersInferenceManager& qim, QuantifiersRegistry& qr,
  TermRegistry& tr)
  : QuantifiersModule(env, qs, qim, qr, tr) 
{
}

MyQuantifiersModule::~MyQuantifiersModule() 
{
}

bool MyQuantifiersModule::needsCheck(Theory::Effort e) 
{
  return true;
}

void MyQuantifiersModule::reset_round(Theory::Effort e) 
{
}

void MyQuantifiersModule::check(Theory::Effort e, QEffort quant_e) 
{
  std::cout << "Hello, World!" << std::endl;
}

std::string MyQuantifiersModule::identify() const
{
  return "my-quantifiers-module";
}

} // namespace quantifiers
} // namespace theory
} // namespace cvc5::internal
