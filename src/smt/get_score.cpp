#include "smt/get_score.h"

#include "expr/e_match.h"
#include "expr/node_algorithm.h"
#include "expr/node_traversal.h"
#include "theory/quantifiers/term_registry.h"

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
  theory::quantifiers::TermDb* d_termDatabase;

  ActiveCandidateCallback(theory::quantifiers::TermDb* termDatabase)
      : CandidateCallback(), d_termDatabase{termDatabase}
  {
  }
  bool consider(TNode candidate) override
  {
    return d_termDatabase->isTermActive(candidate);
  }
};

Score summarizeScore(uint64_t confirmed, uint64_t untrustCex, uint64_t trustCex, uint64_t skipped, uint64_t distinctEqcs, uint64_t rhsEntailed, uint64_t rhsEMatch)
{
  if (TraceIsOn("get-score-summary"))
  {
    std::ostream& out = Trace("get-score-summary");
    out << "confirmed = " << confirmed;
    out << ", untrustCex = " << untrustCex;
    out << ", trustCex = " << trustCex;
    out << ", skipped = " << skipped;
    out << ", distinctEqcs = " << distinctEqcs;
    out << ", rhsEntailed = " << rhsEntailed;
    out << ", rhsEMatch = " << rhsEMatch;
    out << std::endl;
  }

  return std::make_tuple(confirmed, untrustCex, trustCex, skipped);
}

Score getScoreInternal(const TNode& conjecture,
                       QuantifiersEngine* quantifiersEngine)
{
  return getScoreInternal2(conjecture,
                           quantifiersEngine->getTermRegistry(),
                           quantifiersEngine->getEqualityEngine());
}

Score getScoreInternal2(const TNode& conjecture,
                        const theory::quantifiers::TermRegistry& termRegistry,
                        theory::eq::EqualityEngine* equalityEngine)
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

  using theory::quantifiers::EntailmentCheck;

  EntailmentCheck *entailmentCheck = termRegistry.getEntailmentCheck();

  using std::unique_ptr;

  unique_ptr<CandidateCallback> callback(new ActiveCandidateCallback(termRegistry.getTermDatabase()));

  std::cout << equalityEngine->debugPrintEqc();

  EMatch ematch(lhs, callback.get(), equalityEngine);

  uint64_t distinctEqcs = 0;
  uint64_t confirmed = 0;
  uint64_t trustCex = 0;
  uint64_t untrustCex = 0;
  uint64_t rhsEntailed = 0;
  uint64_t rhsEMatch = 0;
  uint64_t skipped = 0;

  for (EqClassesIterator eqcI = EqClassesIterator(equalityEngine);
       !eqcI.isFinished();
       ++eqcI)
  {
    const TNode eqc = *eqcI;

    if (eqc.getType() == lhsType /* && eqc.isConst() */)
    {
      bool confirmedOnOneSubs = false;

      ematch.reset(eqc);

      for (std::optional<Subs> sigma = ematch.next(); sigma;
           sigma = ematch.next())
      {
        Trace("get-score-success")
            << "LHS " << lhs << " is in " << eqc << " under substitution "
            << sigma << std::endl;

        if (Configuration::isDebugBuild())
        {
          const Node lhsImg = sigma->apply(lhs);
          Assert(!expr::hasBoundVar(lhsImg));
          const TNode lhsImgEnt = entailmentCheck->getEntailedTerm(lhsImg);

          Trace("get-score-lhs")
              << "LHS image " << lhsImg << " is entailed equal to " << lhsImgEnt
              << " which is "
              << (equalityEngine->hasTerm(lhsImgEnt) ? "" : "not ")
              << "in the equality engine" << std::endl;

          Assert(lhsImgEnt.isNull()
                 || (equalityEngine->hasTerm(lhsImgEnt)
                     && equalityEngine->areEqual(lhsImgEnt, eqc)));
        }

        const Node rhsImg = sigma->apply(rhs);

        const TNode rhsImgEnt = entailmentCheck->getEntailedTerm(rhsImg);

        Assert(rhsImgEnt.isNull() || equalityEngine->hasTerm(rhsImgEnt));

        if (rhsImgEnt.isNull())
        {
          EMatch ematchRhsImg(rhsImg, callback.get(), equalityEngine);

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

          if (equalityEngine->areEqual(eqc, rhsImgEnt))
          {
            ++confirmed;

            confirmedOnOneSubs = true;
          }
          else if (equalityEngine->areDisequal(eqc, rhsImgEnt, false) || (eqc.isConst() && equalityEngine->getRepresentative(rhsImgEnt).isConst()))
          {
            ++trustCex;

            return summarizeScore(confirmed, untrustCex, trustCex, skipped, distinctEqcs, rhsEntailed, rhsEMatch);
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

  return summarizeScore(confirmed, untrustCex, trustCex, skipped, distinctEqcs, rhsEntailed, rhsEMatch);
}
}  // namespace cvc5::internal
