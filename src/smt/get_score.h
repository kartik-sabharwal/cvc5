#include "cvc5_private.h"

#ifndef CVC5__SMT__GET_SCORE_H
#define CVC5__SMT__GET_SCORE_H

#include "expr/node.h"
#include "expr/subs.h"
#include "theory/theory_model.h"

namespace cvc5::internal {
using theory::TheoryModel;
using SubsLike = std::unordered_map<Node, Node>;
std::tuple<uint64_t, uint64_t, uint64_t> getScoreInternal(const TNode& conjecture,
                                               TheoryModel* theoryModel);
void debugPrintSubtermKinds(const Node term);
Subs subsLikeToSubs(const SubsLike& subsLike);
}  // namespace cvc5::internal

#endif /* CVC5__SMT__GET_SCORE_H */
