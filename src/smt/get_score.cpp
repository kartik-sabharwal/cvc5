#include "smt/get_score.h"

#include "expr/e_match.h"
#include "expr/node_algorithm.h"
#include "expr/node_traversal.h"

namespace cvc5::internal {
using theory::eq::EqClassesIterator;
using theory::eq::EqClassIterator;
using theory::eq::EqualityEngine;

class MyCandidateCallback : public CandidateCallback
{
 public:
  bool consider(CVC5_UNUSED Node cand) override { return true; }
};

std::tuple<uint64_t, uint64_t, uint64_t> getScoreInternal(const TNode& conjecture,
                                               TheoryModel* theoryModel)
{
  Assert(conjecture.getKind() == Kind::FORALL);

  const TNode& body = conjecture[1];

  Assert(body.getKind() == Kind::EQUAL);

  const TNode& lhs = body[0];
  const TNode& rhs = body[1];

  const TypeNode& lhsType = lhs.getType();

  std::unique_ptr<MyCandidateCallback> callback(new MyCandidateCallback());

  EqualityEngine* eqEng = theoryModel->getEqualityEngine();

  EMatch ematch(lhs, callback.get(), eqEng);

  uint64_t tested = 0;
  uint64_t confirmed = 0;
  uint64_t skipped = 0;

  for (EqClassesIterator eqc = EqClassesIterator(eqEng); !eqc.isFinished();
       ++eqc)
  {
    if ((*eqc).getType() == lhsType)
    {
      ematch.reset(*eqc);

      std::optional<Subs> sigma = ematch.next();

      while (sigma)
      {
        const Node lhsImg = sigma->apply(lhs);

        if (expr::hasBoundVar(lhsImg))
        {
          Trace("get-score") << "Image " << lhsImg << " of LHS term " << lhs << " has free variables!" << std::endl;
          
          Assert(false);
        }

        const Node rhsImg = sigma->apply(rhs);

        if (eqEng->hasTerm(rhsImg))
        {
          ++tested;

          if (eqEng->areEqual(rhsImg, *eqc))
          {
            ++confirmed;
          }
        }
        else
        {
          ++skipped;
        }

        sigma = ematch.next();
      }
    }
  }

  return std::make_tuple(confirmed, tested, skipped);
}

Subs subsLikeToSubs(const SubsLike& subsLike)
{
  Subs sigma;

  for (SubsLike::const_iterator entry = subsLike.begin();
       entry != subsLike.end();
       ++entry)
  {
    sigma.add(std::get<0>(*entry), std::get<1>(*entry));
  }

  return sigma;
}

void debugPrintSubtermKinds(const Node term)
{
  const NodeDfsIterable subterms = NodeDfsIterable(term);
  NodeDfsIterator subtermsEnd = subterms.end();
  for (NodeDfsIterator subterm = subterms.begin(); subterm != subtermsEnd;
       ++subterm)
  {
    std::cout << "kind " << *subterm << " is " << subterm.operator*().getKind()
              << std::endl;
  }
}
}  // namespace cvc5::internal
