#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__UNROLL_H
#define CVC5__PREPROCESSING__PASSES__UNROLL_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class Unroll : public PreprocessingPass
{
 public:
  Unroll(PreprocessingPassContext* ppc);
 protected:
  PreprocessingPassResult applyInternal(AssertionPipeline* ap) override;
 private:
  bool d_first_time;
  typedef std::tuple<Node, std::vector<Node>, size_t, std::vector<Node>> AbstractionData;
  /**
   * Extract the information necessary to unroll the definition of the function symbol func.
   */
  AbstractionData makeAbstraction(const Node func, const std::vector<Node> formals, const Node formula);
  /**
   * Print all the components of a node along with their kinds.
   */
  void deconstruct(const Node expr);
  /**
   * Freshen all the variables bound in the MATCH_BIND_CASE.
   */
  Node uniquify(const Node body);
  /**
   * Actually perform the unrolling.
   */
  Node unroll(const Node func, const std::vector<Node> formals, const Node formula, const size_t count);
  /**
   * Collect the uninterpreted function symbols that appear outside of
   * universally or existentially quantified subformulas.
   */
  const std::unordered_set<Node> getFuncSyms(TNode phi) const;
};

} // namespace passes
} // namespace preprocessing
} // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__UNROLL_H */
