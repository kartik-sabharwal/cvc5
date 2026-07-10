#include "expr/e_match.h"

#include "expr/node_algorithm.h"

namespace cvc5::internal {
std::ostream& operator<<(ostream& out, const Positions& st)
{
  out << "begin operator<<" << std::endl;

  out << "{";
  for (const size_t elem : st)
  {
    out << " " << elem;
  }
  out << " }";

  out << "end operator<<" << std::endl;

  return out;
}

Pattern::Pattern(Node pat,
                 Node eqc,
                 CandidateCallback* candCallback,
                 EqualityEngine* eqEng)
    : d_pat(pat),
      d_nextCandPosn(0),
      d_subPatPosns(),
      d_varPosns(),
      d_boundPosns()

{
  Assert(d_pat.hasOperator());

  const Node op = pat.getOperator();

  PositionToNode posnToGround;

  for (size_t posn = 0; posn != d_pat.getNumChildren(); ++posn)
  {
    Node child = d_pat[posn];

    if (child.getKind() == Kind::BOUND_VARIABLE)
    {
      d_varPosns.insert(posn);
    }
    else if (expr::hasBoundVar(child))
    {
      d_subPatPosns.insert(posn);
    }
    else
    {
      posnToGround[posn] = child;
    }
  }

  for (EqClassIterator termIter = EqClassIterator(eqc, eqEng);
       !termIter.isFinished();
       ++termIter)
  {
    const Node term = *termIter;

    if (term.hasOperator() && term.getOperator() == op
        && candCallback->consider(term))
    {
      bool addToCands = true;

      for (PositionToNode::const_iterator entry =
               posnToGround.begin();
           entry != posnToGround.end();
           ++entry)
      {
        const Node termChild = term[std::get<0>(*entry)];
        const Node patChild = std::get<1>(*entry);

        Assert(eqEng->hasTerm(termChild));

        if (!eqEng->hasTerm(patChild))
        {
          Assert(termChild != patChild);

          addToCands = false;
        }
        else if (eqEng->areDisequal(termChild, patChild, false))
        {
          addToCands = false;
        }
      }

      if (addToCands)
      {
        d_cands.push_back(term);
      }
    }
  }

  // We want to inspect that the positions of all bound variables have been
  // recorded!
  {
    ostream& out = Trace("e-match");
    out << "Pattern {" << std::endl;
    out << "d_pat := " << d_pat << std::endl;
    out << "d_varPosns := ";
    debugPrintPosns(d_varPosns, d_pat, out);
    out << std::endl;
    out << "d_subPatPosns := ";
    debugPrintPosns(d_subPatPosns, d_pat, out);
    out << std::endl;
    out << "}" << std::endl;
  }
}

MaybeJobs Pattern::next(Subs& subs, EqualityEngine* eqEng)
{
  for (; d_nextCandPosn != d_cands.size(); ++d_nextCandPosn)
  {
    const Node cand = d_cands[d_nextCandPosn];

    bool failure = false;

    PositionToNode newSubs;

    for (Positions::const_iterator posnIter = d_varPosns.begin();
         posnIter != d_varPosns.end();
         ++posnIter)
    {
      const size_t posn = *posnIter;
      const Node var = d_pat[posn];
      const Node img = cand[posn];
      const bool inSubs = subs.contains(var);
      const bool inNewSubs = newSubs.find(posn) != newSubs.end();

      if ((inSubs && eqEng->areDisequal(subs.getSubs(var), img, false))
          || (inNewSubs && eqEng->areDisequal(newSubs[posn], img, false)))
      {
        failure = true;
        break;
      }
      else if (!inSubs && !inNewSubs)
      {
        newSubs[posn] = img;
      }
    }

    if (failure)
    {
      continue;
    }

    Jobs newJobs;

    for (Positions::const_iterator posn = d_subPatPosns.begin();
         posn != d_subPatPosns.end();
         ++posn)
    {
      newJobs.emplace_back(d_pat[*posn], eqEng->getRepresentative(cand[*posn]));
    }

    ++d_nextCandPosn;

    for (PositionToNode::const_iterator entry = newSubs.begin();
         entry != newSubs.end();
         ++entry)
    {
      const size_t boundPosn = std::get<0>(*entry);

      const Node img = std::get<1>(*entry);

      subs.add(d_pat[boundPosn], std::get<1>(*entry));

      d_boundPosns.insert(boundPosn);
    }

    {
      ostream& out = Trace("e-match");
      out << "Pattern::next for " << d_pat << " {" << std::endl;
      for (Positions::const_iterator posn = d_varPosns.cbegin();
           posn != d_varPosns.end();
           ++posn)
      {
        const TNode& var = d_pat[*posn];
        out << "Child variable " << var;
        if (subs.contains(var))
        {
          out << " bound." << std::endl;
        }
        else
        {
          out << " unbound!" << std::endl;
        }
      }
      out << "}" << std::endl;
    }

    return MaybeJobs(newJobs);
  }

  return MaybeJobs();
}

void Pattern::backtrack(Subs& subs)
{
  for (Positions::const_iterator boundPosn = d_boundPosns.begin();
       boundPosn != d_boundPosns.end();
       ++boundPosn)
  {
    const size_t boundPosnValue = *boundPosn;

    Assert(boundPosnValue < d_pat.getNumChildren());

    const Node var = d_pat[boundPosnValue];

    Assert(subs.contains(var));

    subs.erase(d_pat[*boundPosn]);
  }

  d_boundPosns.clear();
}

void Pattern::debugPrintPosns(const Positions& posns, const TNode& term, ostream& out)
{
  out << "{";
  Positions::const_iterator posn = posns.cbegin();
  const Positions::const_iterator posnsEnd = posns.cend();
  if (posn != posnsEnd)
  {
    out << *posn << " = " << term[*posn];

    ++posn;
  }
  for (; posn != posnsEnd; ++posn)
  {
    out << ", " << *posn << " = " << term[*posn];
  }
  out << "}";
}

EMatch::EMatch(Node pat,
               CandidateCallback* candCallback,
               EqualityEngine* eqEng)
    : d_pat(pat),
      d_eqc(Node::null()),
      d_candCallback(candCallback),
      d_eqEng(eqEng)
{
}

void EMatch::reset(Node eqc)
{
  d_eqc = eqc;

  d_subPats.clear();
  d_subPats.emplace_back(new Pattern(d_pat, d_eqc, d_candCallback, d_eqEng));

  d_cursor = 0;

  d_subs.clear();
}

void EMatch::backtrack()
{
  --d_cursor;

  d_subPats[d_cursor]->backtrack(d_subs);
}

MaybeSubs EMatch::next()
{
  MaybeSubs result;

  debugPrintState(Trace("e-match"));
  Trace("e-match") << std::endl;

  while (d_cursor < d_subPats.size())
  {
    MaybeJobs newJobs = d_subPats[d_cursor]->next(d_subs, d_eqEng);

    if (newJobs)
    {
      for (Jobs::const_iterator entry = newJobs->begin();
           entry != newJobs->end();
           ++entry)
      {
        const Node pat = std::get<0>(*entry);
        const Node eqc = std::get<1>(*entry);
        d_subPats.emplace_back(new Pattern(pat, eqc, d_candCallback, d_eqEng));
      }

      ++d_cursor;
    }
    else
    {
      for (CVC5_UNUSED size_t i = d_cursor; d_cursor < d_subPats.size(); ++i)
      {
        d_subPats.pop_back();
      }

      if (d_cursor > 0)
      {
        backtrack();
      }
    }

    debugPrintState(Trace("e-match"));
    Trace("e-match") << std::endl;
  }

  Assert(d_cursor == d_subPats.size());

  if (d_cursor > 0)
  {
    result = d_subs;

    Trace("e-match") << "EMatch::next {" << std::endl;
    Trace("e-match") << "Before backtrack(), result := " << result << std::endl;

    backtrack();

    Trace("e-match") << "After backtrack(), result := " << result << std::endl;
    Trace("e-match") << "}" << std::endl;
  }

  return result;
}

void EMatch::debugPrintState(ostream& out)
{
  out << "[";
  if (!d_subPats.empty())
  {
    if (d_cursor == 0) out << "!";

    out << d_subPats[0]->d_pat;
  }
  for (size_t i = 1; i < d_subPats.size(); ++i)
  {
    out << ", ";

    if (d_cursor == i) out << "!";

    out << d_subPats[i]->d_pat;
  }
  out << "]";
  if (d_cursor == d_subPats.size()) out << "!";
}
}  // namespace cvc5::internal
