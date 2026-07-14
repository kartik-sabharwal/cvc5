#include "smt/get_score.h"

#include "expr/e_match.h"
#include "expr/node_algorithm.h"
#include "expr/node_traversal.h"

namespace cvc5::internal {
using theory::eq::EqClassesIterator;
using theory::eq::EqClassIterator;
using theory::eq::EqualityEngine;

class SimpleCandidateCallback : public CandidateCallback
{
 public:
  bool consider(CVC5_UNUSED TNode cand) override { return true; }
};

class ActiveCandidateCallback : public CandidateCallback
{
 public:
  QuantifiersEngine* d_quantEng;

  ActiveCandidateCallback(QuantifiersEngine* quantEng)
      : CandidateCallback(), d_quantEng(quantEng)
  {
  }
  bool consider(TNode cand) override { return d_quantEng->isTermActive(cand); }
};

Score getScoreInternal(const TNode& conjecture, QuantifiersEngine* quantEng)
{
  Assert(conjecture.getKind() == Kind::FORALL);

  const TNode& body = conjecture[1];

  Assert(body.getKind() == Kind::EQUAL);

  const TNode& lhs = body[0];
  const TNode& rhs = body[1];
  const TypeNode& lhsType = lhs.getType();

  if (Configuration::isDebugBuild())
  {
    std::unordered_set<Node> lhsVars;
    std::unordered_set<Node> rhsVars;
    std::set<Node> lhsVarsSorted;
    std::set<Node> rhsVarsSorted;
    expr::getSubtermsKind(Kind::BOUND_VARIABLE, lhs, lhsVars, false);
    expr::getSubtermsKind(Kind::BOUND_VARIABLE, rhs, rhsVars, false);
    lhsVarsSorted.insert(lhsVars.cbegin(), lhsVars.cend());
    rhsVarsSorted.insert(rhsVars.cbegin(), rhsVars.cend());
    Assert(std::includes(lhsVarsSorted.cbegin(),
                         lhsVarsSorted.cend(),
                         rhsVarsSorted.cbegin(),
                         rhsVarsSorted.cend()));
  }

  std::unique_ptr<CandidateCallback> callback(
      new ActiveCandidateCallback(quantEng));

  EqualityEngine* ee = quantEng->getEqualityEngine();

  EMatch ematch(lhs, callback.get(), ee);

  uint64_t distinctEqcs = 0;
  uint64_t confirmed = 0;
  uint64_t trustCex = 0;
  uint64_t untrustCex = 0;
  uint64_t rhsEntailed = 0;
  uint64_t rhsEMatch = 0;
  uint64_t skipped = 0;

  for (EqClassesIterator eqcI = EqClassesIterator(ee); !eqcI.isFinished();
       ++eqcI)
  {
    const TNode eqc = *eqcI;

    if (eqc.getType() == lhsType && eqc.isConst())
    {
      bool confirmedOnOneSubs = false;

      ematch.reset(eqc);

      for (std::optional<Subs> sigma = ematch.next(); sigma;
           sigma = ematch.next())
      {
        if (Configuration::isDebugBuild())
        {
          const Node lhsImg = sigma->apply(lhs);
          Assert(!expr::hasBoundVar(lhsImg));
          const TNode lhsImgEnt = quantEng->getEntailedTerm(lhsImg);
          Assert(lhsImgEnt.isNull()
                 || (ee->hasTerm(lhsImgEnt) && ee->areEqual(lhsImgEnt, eqc)));
        }

        const Node rhsImg = sigma->apply(rhs);
        const TNode rhsImgEnt = quantEng->getEntailedTerm(rhsImg);

        Assert(rhsImgEnt.isNull() || ee->hasTerm(rhsImgEnt));

        if (rhsImgEnt.isNull())
        {
          EMatch ematchRhsImg(rhsImg, callback.get(), ee);

          ematchRhsImg.reset(eqc);

          if (ematchRhsImg.next().has_value())
          {
            ++rhsEMatch;

            ++confirmed;

            confirmedOnOneSubs = true;

            if (TraceIsOn("get-score-rhs"))
            {
              std::ostream& out = Trace("get-score-rhs");
              out << "* " << rhsImg << " == " << eqc << std::endl;
            }
          }
          else
          {
            ++skipped;
          }
        }
        else
        {
          ++rhsEntailed;

          if (ee->areEqual(eqc, rhsImgEnt))
          {
            ++confirmed;

            confirmedOnOneSubs = true;
          }
          else if (ee->getRepresentative(rhsImgEnt).isConst())
          {
            ++trustCex;
          }
          else
          {
            ++untrustCex;
          }
        }
      }

      if (confirmedOnOneSubs)
      {
        ++distinctEqcs;
      }
    }
  }

  if (TraceIsOn("get-score-summary"))
  {
    std::ostream& out = Trace("get-score-summary");
    out << "confirmed = " << confirmed;
    out << ", distinctEqcs = " << distinctEqcs;
    out << ", trustCex = " << trustCex;
    out << ", untrustCex = " << untrustCex;
    out << ", skipped = " << skipped;
    out << ", rhsEntailed = " << rhsEntailed;
    out << ", rhsEMatch = " << rhsEMatch;
    out << std::endl;
  }

  return std::make_tuple(confirmed, confirmed + trustCex + untrustCex, skipped);
}
}  // namespace cvc5::internal
