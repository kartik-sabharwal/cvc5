#include "cvc5_private.h"

#ifndef CVC5__EXPR__E_MATCH_H
#define CVC5__EXPR__E_MATCH_H

#include "expr/node.h"
#include "expr/subs.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
using std::ostream;
using theory::eq::EqualityEngine;
using theory::eq::EqClassIterator;
typedef std::unordered_set<size_t> Positions;
typedef std::vector<Node> Nodes;
typedef std::pair<Node, Node> Job;
typedef std::vector<Job> Jobs;
typedef std::optional<Jobs> MaybeJobs;
typedef std::optional<Subs> MaybeSubs;
typedef std::unordered_map<size_t, Node> PositionToNode;

class CandidateCallback
{
 public:
  CandidateCallback() {}
  virtual ~CandidateCallback() {}
  virtual bool consider(Node cand) = 0;
};

class Pattern
{
 public:
  Pattern(Node pat,
          Node eqc,
          CandidateCallback* candCallback,
          EqualityEngine* eqEng);

  /**
   * We want to find matches for this d_pat.  We assume that d_pat.getKind() is
   * an atomic trigger kind.  See TriggerTermInfo::isAtomicTriggerKind() to
   * learn what this means.
   */
  Node d_pat;

  /**
   * We want to try matching d_pat against all these terms.
   */
  Nodes d_cands;

  /**
   * When next() is called we will try to match d_pat with
   * d_cands[d_nextCandPosn].
   */
  size_t d_nextCandPosn;

  /**
   * i is in d_subPatPosns if and only if d_pat[i] is not a matchable variable.
   */
  Positions d_subPatPosns;

  /**
   * i is in d_varPosns if and only if d_pat[i] is a matchable variable.
   */
  Positions d_varPosns;

  /**
   * i is in d_boundPosns if and only if this Pattern object added a mapping
   * for d_pat[i] to its owner's d_subs field during a call to next().  It
   * follows that this object should erase exactly those mappings during a call
   * to backtrack().
   */
  Positions d_boundPosns;

  MaybeJobs next(Subs& subs, EqualityEngine* eqEng);

  void backtrack(Subs& subs);

 private:
  void debugPrintPosns(const Positions& posns,
                       const TNode& term,
                       ostream& out);
};

typedef std::vector<std::unique_ptr<Pattern>> Patterns;

class EMatch
{
 public:
  EMatch(Node pat,
         CandidateCallback* candCallback,
         EqualityEngine* eqEng);

  /**
   * The pattern that needs to be unified with the equivalence class d_eqc.
   */
  Node d_pat;

  /**
   * The equivalence class to match d_pat with.
   */
  Node d_eqc;

  /**
   * We will skip any candidate for which the following callback returns false.
   */
  CandidateCallback* d_candCallback;

  /**
   * A pointer to an equality engine.
   */
  EqualityEngine* d_eqEng;

  /**
   * The vector of non-variable sub-patterns of d_pat.
   *
   * We build this vector such that if the (non-variable) sub-pattern p appears
   * before the sub-pattern p' in a breadth-first traversal of d_pat then p
   * appears before p' in d_subPats.
   *
   * For example, if d_pat is plus(times(X, plus(Succ(Zero), Y)), times(X, Z))
   * is a pattern with matchable variables X, Y and Z, then at some point in the
   * e-matching process d_subPats might look like:
   *
   * d_subPats[0] := plus(times(X, plus(Succ(Zero), Y)), times(X, Z))
   * d_subPats[1] := times(X, plus(Succ(Zero)))
   * d_subPats[2] := times(X, Z)
   * d_subPats[3] := plus(Succ(Zero))
   * d_subPats[4] := Succ(Zero)
   * d_subPats[5] := Zero
   */
  Patterns d_subPats;

  /**
   * An e-matching attempt is successful when d_cursor is exactly
   * d_subPats.size().
   */
  size_t d_cursor;

  /**
   * The current substitution.
   */
  Subs d_subs;

  /**
   * Resets to the initial state trying to match d_pat with eqc.  Needless to
   * say, sets d_eqc to eqc.
   */
  void reset(Node eqc);

  void backtrack();

  /**
   * Returns an empty optional if and only if there are no more substitutions
   * that make d_pat equivalent to d_eqc.  Otherwise returns an optional that
   * contains a substitution sigma.  sigma is a shallow copy of d_subs so sigma
   * and d_subs can be modified independently.
   */
  MaybeSubs next();

  void debugPrintState(ostream& out);
};
}  // namespace cvc5::internal

#endif /* CVC5__EXPR__E_MATCH_H */
