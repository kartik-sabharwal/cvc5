#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__CONE_OF_INFLUENCE_H
#define CVC5__PREPROCESSING__PASSES__CONE_OF_INFLUENCE_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class ConeOfInfluence : public PreprocessingPass
{
 public:
  ConeOfInfluence(PreprocessingPassContext* ppc);
 protected:
  /**
   * We iterate over all assertions.  As we do this we map the position of each
   * assertion in the pipeline, its "serial number", to a set of uninterpreted
   * function symbols and constant symbols.  We also prepare a map that
   * associates ach function and constant symbol to the set of positions that
   * mention the symbol.  Furthermore we record the positions of all negated
   * assertions as our "itinerary".  We use the itinerary to start a depth-first
   * search over assertions.  In each "step" of this DFS we pop a position from
   * the itinerary, add the position to a set of "visited" positions, then for
   * each symbol that occurs at the position we are visiting, we add the
   * positions that mention that symbol to the itinerary.  If the position we
   * are visiting is already in the visited set we do nothing and move on to the
   * next position in the itinerary.  For any position that is *not* in the
   * visited set we change that assertion to true.
   */
  PreprocessingPassResult applyInternal(AssertionPipeline* ap) override;
 private:
  template <class T>
  bool member(std::unordered_set<T>& st, const T& elt)
  {
    return st.find(elt) != st.end();
  }
};

} // namespace passes
} // namespace preprocessing
} // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__CONE_OF_INFLUENCE_H */
