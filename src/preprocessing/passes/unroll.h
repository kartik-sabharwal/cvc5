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
  /**
   * Actually perform the unrolling.
   */
  Node unroll(const Node phi, size_t fuel);
  /**
   * Collect the uninterpreted function symbols that appear outside of
   * universally or existentially quantified subformulas.
   */
  const std::unordered_set<Node> getFuncSyms(TNode phi) const;
  Node elimAndOr(const Node expr);
  Node baseCase(const Node func, const Node expr);
};

} // namespace passes
} // namespace preprocessing
} // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__UNROLL_H */
