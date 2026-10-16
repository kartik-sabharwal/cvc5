#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__TRUSTED_ENVIRONMENT_H
#define CVC5__THEORY__QUANTIFIERS__TRUSTED_ENVIRONMENT_H

#include "theory/smt_engine_subsolver.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"

namespace cvc5::internal::theory::quantifiers {

class TrustedEnvironment
{
 private:
  /** Exactly the collection of formulas that have been asserted to d_subsolver. */
  std::vector<Node> d_assertedFormulas;

  /**
   * A subsolver that asserts exactly d_assertedFormulas.
   * It's initialized in the constructor, TrustedEnvironment.
   */
  std::unique_ptr<SolverEngine> d_subsolver;

  /** When we prove something new we also send it here with addPendingLemma. */
  QuantifiersInferenceManager& d_inferenceManager;

 public:
  /** Constructor. */
  TrustedEnvironment(QuantifiersInferenceManager& inferenceManager, const Options& options, const Env& environment);

  /** Adds 'formula' to d_assertedFormulas and calls d_subsolver.assertFormula(formula). */
  void assertFormula(const Node& formula);

  /**
   * Checks that 'formula' is provable from d_assertedFormulas, possibly by induction i.e. that 'formula' is inductively entailed.
   * It does this by checking the satisfiability of d_assertedFormulas under the assumption not(formula) through d_subsolver.
   * If the query returns UNSAT then we
   *
   *   1. call assertFormula(formula), and
   *   2. call d_inferenceManager.addPendingLemma(formula, InferenceId::QUANTIFIERS_ENUMERATIVE_CONJECTURE_GENERATOR)
   *   3. return 'true'
   * 
   * On the other hand if the query returns UNKNOWN or SAT (I can't imagine how it could return SAT) we just return 'false'.
   */
  bool prove(const Node& formula);
};

} // namespace cvc5::internal::theory::quantifiers

#endif /* CVC5__THEORY__QUANTIFIERS__TRUSTED_ENVIRONMENT_H */
