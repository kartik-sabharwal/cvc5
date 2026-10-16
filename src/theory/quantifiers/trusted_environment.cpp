#include "theory/quantifiers/trusted_environment.h"

#include "options/options.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "smt/set_defaults.h"

namespace cvc5::internal::theory::quantifiers {
TrustedEnvironment::TrustedEnvironment(QuantifiersInferenceManager& inferenceManager, const Options& options, const Env& environment) : d_inferenceManager(inferenceManager)
{
  Options subsolverOptions;

  subsolverOptions.copyValues(options);

  { // Begin setting base options.
    options::HolderBASE& holder = subsolverOptions.write_base();
    holder.incrementalSolving = true;
  } // End setting base options.

  { // Begin setting quantifiers options.
    options::HolderQUANTIFIERS& holder = subsolverOptions.write_quantifiers();
    holder.quantInduction = true;
    holder.dtStcInduction = true;
    holder.conjectureGen = false;
    holder.enumerativeConjectureGenerator = false;
    holder.contextualEnumerator = false;
    holder.quantSubCbqi = false;
  } // End setting quantifiers options.

  smt::SetDefaults::disableChecking(subsolverOptions);

  SubsolverSetupInfo setupInfo(environment, subsolverOptions);

  initializeSubsolver(environment.getNodeManager(), d_subsolver, setupInfo, true, options.quantifiers.ecgSubsolverTimeout);
}

void TrustedEnvironment::assertFormula(const Node& formula)
{
  d_assertedFormulas.push_back(formula);

  d_subsolver->assertFormula(formula);
}

bool TrustedEnvironment::prove(const Node& goal)
{
  bool proved = false;

  const Node negatedGoal = goal.negate();

  const Result result = d_subsolver->checkSat(negatedGoal);

  switch (result.getStatus())
  {
    case Result::UNSAT:
    {
      proved = true;

      assertFormula(goal);

      d_inferenceManager.addPendingLemma(goal, InferenceId::QUANTIFIERS_ENUMERATIVE_CONJECTURE_GENERATOR);
      
      break;
    }

    default:
    {
      proved = false;

      break;
    }
  }

  return proved;
}
} // namespace cvc5::internal::theory::quantifiers
