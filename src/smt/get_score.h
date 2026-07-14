#include "cvc5_private.h"

#ifndef CVC5__SMT__GET_SCORE_H
#define CVC5__SMT__GET_SCORE_H

#include "expr/node.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_model.h"

namespace cvc5::internal {

using theory::QuantifiersEngine;
using theory::TheoryModel;
typedef std::tuple<uint64_t, uint64_t, uint64_t> Score;

Score getScoreInternal(const TNode& conjecture, QuantifiersEngine* quantEng);

}  // namespace cvc5::internal

#endif /* CVC5__SMT__GET_SCORE_H */
