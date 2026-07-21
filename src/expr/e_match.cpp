#include "expr/e_match.h"

#include "expr/node_algorithm.h"

namespace cvc5::internal {
std::ostream& operator<<(ostream& out, const Positions& st)
{
  out << "{";
  for (const size_t elem : st)
  {
    out << " " << elem;
  }
  out << " }";
  return out;
}

Pattern::Pattern(Node pat)
    : d_pat(pat),
      d_cands(),
      d_nextCandPosn(0),
      d_subPatPosns(),
      d_varPosns(),
      d_groundPosns(),
      d_boundPosns(),
      d_subPatIdxs()
{
  populateSubPatVarGroundPosns();
}

void Pattern::populateSubPatVarGroundPosns()
{
  for (size_t i = 0; i < d_pat.getNumChildren(); ++i)
  {
    const Node child = d_pat[i];

    if (child.getKind() == Kind::BOUND_VARIABLE)
    {
      d_varPosns.push_back(i);
    }
    else if (expr::hasBoundVar(child))
    {
      d_subPatPosns.push_back(i);
    }
    else
    {
      d_groundPosns.push_back(i);
    }
  }
}

void Pattern::reset(const Node eqc,
                    CandidateCallback* callback,
                    EqualityEngine* ee)
{
  populateCands(eqc, callback, ee);

  d_nextCandPosn = 0;

  d_boundPosns.clear();
}

void Pattern::populateCands(const Node eqc,
                            CandidateCallback* callback,
                            EqualityEngine* ee)
{
  d_cands.clear();

  for (EqClassIterator termI = EqClassIterator(eqc, ee); !termI.isFinished();
       ++termI)
  {
    const Node term = *termI;

    if (term.hasOperator() && term.getOperator() == d_pat.getOperator()
        && callback->consider(term) && checkGroundPosns(term, ee))
    {
      d_cands.push_back(term);
    }
  }
}

bool Pattern::checkGroundPosns(const Node term, EqualityEngine* ee)
{
  for (Positions::const_iterator posnI = d_groundPosns.cbegin();
       posnI != d_groundPosns.cend();
       ++posnI)
  {
    const size_t posn = *posnI;
    const Node termChild = term[posn];
    const Node patChild = d_pat[posn];

    if (ee->hasTerm(patChild) && ee->hasTerm(termChild) && ee->areEqual(patChild, termChild))
    {
      continue;
    }
    else if (patChild == termChild)
    {
      continue;
    }
    else
    {
      return false;
    }
  }

  return true;
}

MaybeJobs Pattern::next(Subs& subs, EqualityEngine* ee)
{
  for (; d_nextCandPosn != d_cands.size(); ++d_nextCandPosn)
  {
    const Node cand = d_cands[d_nextCandPosn];

    MaybePositionToNode mappings = getMappings(cand, subs, ee);

    if (mappings)
    {
      commitMappings(*mappings, subs);

      Jobs newJobs = getNewJobs(cand, ee);

      ++d_nextCandPosn;

      return MaybeJobs(newJobs);
    }
  }

  return MaybeJobs();
}

MaybePositionToNode Pattern::getMappings(const Node cand,
                                         Subs& subs,
                                         EqualityEngine* ee)
{
  PositionToNode mappings;

  for (Positions::const_iterator posnI = d_varPosns.begin();
       posnI != d_varPosns.end();
       ++posnI)
  {
    const size_t posn = *posnI;

    const Node var = d_pat[posn];
    const Node img = cand[posn];

    const bool varInSubs = subs.contains(var);
    const bool varInMappings = mappings.find(posn) != mappings.end();

    Assert(varInSubs ? ee->hasTerm(subs.getSubs(var)) : true);
    Assert(varInMappings ? ee->hasTerm(mappings.at(posn)) : true);
    Assert(ee->hasTerm(img));

    if ((varInSubs && !ee->areEqual(subs.getSubs(var), img))
        || (varInMappings && !ee->areEqual(mappings.at(posn), img)))
    {
      return MaybePositionToNode();
    }
    else if (!varInSubs && !varInMappings)
    {
      mappings[posn] = img;
    }
  }

  return MaybePositionToNode(mappings);
}

void Pattern::commitMappings(const PositionToNode& mappings, Subs& subs)
{
  for (PositionToNode::const_iterator entry = mappings.begin();
       entry != mappings.end();
       ++entry)
  {
    const size_t boundPosn = std::get<0>(*entry);
    const Node img = std::get<1>(*entry);

    subs.add(d_pat[boundPosn], img);

    d_boundPosns.push_back(boundPosn);
  }
}

Jobs Pattern::getNewJobs(const Node cand, EqualityEngine* ee)
{
  Jobs result;

  for (size_t i = 0; i < d_subPatPosns.size(); ++i)
  {
    const size_t jobIdx = d_subPatIdxs[i];
    const Node jobEqc = ee->getRepresentative(cand[d_subPatPosns[i]]);
    result.emplace_back(jobIdx, jobEqc);
  }

  return result;
}

void Pattern::addChildren(Patterns& subPats)
{
  for (Positions::const_iterator posnI = d_subPatPosns.cbegin();
       posnI != d_subPatPosns.cend();
       ++posnI)
  {
    const size_t posn = *posnI;
    const Node subPat = d_pat[posn];
    d_subPatIdxs.push_back(subPats.size());
    subPats.emplace_back(new Pattern(subPat));
  }
}

void Pattern::backtrack(Subs& subs)
{
  for (Positions::const_iterator posnI = d_boundPosns.cbegin();
       posnI != d_boundPosns.cend();
       ++posnI)
  {
    subs.erase(d_pat[*posnI]);
  }

  d_boundPosns.clear();
}

void Pattern::debugPrintPosns(const Positions& posns,
                              const TNode& term,
                              ostream& out)
{
  out << "{";
  Positions::const_iterator posnI = posns.cbegin();
  if (posnI != posns.cend())
  {
    const size_t posn = *posnI;
    out << posn << " = " << term[posn];
    ++posnI;
  }
  for (; posnI != posns.cend(); ++posnI)
  {
    const size_t posn = *posnI;
    out << ", " << posn << " = " << term[posn];
  }
  out << "}";
}

EMatch::EMatch(Node pat, CandidateCallback* callback, EqualityEngine* ee)
    : d_pat(pat), d_eqc(Node::null()), d_callback(callback), d_ee(ee)
{
  populateSubPats();
}

void EMatch::populateSubPats()
{
  d_subPats.emplace_back(new Pattern(d_pat));

  size_t i = 0;

  while (i < d_subPats.size())
  {
    d_subPats.at(i)->addChildren(d_subPats);

    ++i;
  }
}

void EMatch::reset(Node eqc)
{
  d_eqc = eqc;

  d_subPats.at(0)->reset(eqc, d_callback, d_ee);

  d_cursor = 0;

  d_subs.clear();
}

MaybeSubs EMatch::next()
{
  while (d_cursor < d_subPats.size())
  {
    debugPrintState(Trace("e-match"));

    MaybeJobs jobs = d_subPats.at(d_cursor)->next(d_subs, d_ee);

    if (jobs)
    {
      ++d_cursor;

      for (Jobs::const_iterator entry = jobs->cbegin(); entry != jobs->cend();
           ++entry)
      {
        const size_t idx = std::get<0>(*entry);
        const Node eqc = std::get<1>(*entry);
        d_subPats.at(idx)->reset(eqc, d_callback, d_ee);
      }
    }
    else if (d_cursor > 0)
    {
      --d_cursor;

      d_subPats.at(d_cursor)->backtrack(d_subs);
    }
    else
    {
      break;
    }
  }

  debugPrintState(Trace("e-match"));

  MaybeSubs result;

  if (d_cursor > 0)
  {
    result = MaybeSubs(d_subs);

    --d_cursor;

    d_subPats.at(d_cursor)->backtrack(d_subs);
  }

  return result;
}

void EMatch::debugPrintCandidate(const size_t patternPosition, ostream& out)
{
  const size_t nextCandidatePosition = d_subPats[patternPosition]->d_nextCandPosn;

  if (nextCandidatePosition == 0)
  {
    out << "X";
  }
  else
  {
    out << d_subPats[patternPosition]->d_cands[nextCandidatePosition - 1];
  }
}

void EMatch::debugPrintState(ostream& out)
{
  out << "EMatch::debugPrintState {" << std::endl;
  out << "[";
  if (!d_subPats.empty())
  {
    if (d_cursor == 0)
    {
      out << "!";
    }
    out << d_subPats[0]->d_pat << " with "; 
    debugPrintCandidate(0, out);
  }
  for (size_t i = 1; i < d_subPats.size(); ++i)
  {
    out << ", ";
    if (d_cursor == i)
    {
      out << "!";
    }
    out << d_subPats[i]->d_pat << " with ";
    debugPrintCandidate(i, out);
  }
  out << "]";
  if (d_cursor == d_subPats.size())
  {
    out << "!";
  }
  out << std::endl;
  out << d_subs << std::endl;
  out << "}" << std::endl;
}
}  // namespace cvc5::internal
