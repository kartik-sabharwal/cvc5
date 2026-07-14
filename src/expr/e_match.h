#include "cvc5_private.h"

#ifndef CVC5__EXPR__E_MATCH_H
#define CVC5__EXPR__E_MATCH_H

#include "expr/node.h"
#include "expr/subs.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
class Pattern;

using std::ostream;
using theory::eq::EqClassIterator;
using theory::eq::EqualityEngine;
typedef std::vector<size_t> Positions;
typedef std::vector<size_t> Indices;
typedef std::vector<Node> Nodes;
typedef std::pair<size_t, Node> Job;
typedef std::vector<Job> Jobs;
typedef std::optional<Jobs> MaybeJobs;
typedef std::optional<Subs> MaybeSubs;
typedef std::unordered_map<size_t, Node> PositionToNode;
typedef std::optional<PositionToNode> MaybePositionToNode;
typedef std::vector<std::unique_ptr<Pattern>> Patterns;
typedef std::vector<size_t> PositionToIndex;

class CandidateCallback
{
 public:
  CandidateCallback() {}
  virtual ~CandidateCallback() {}
  virtual bool consider(TNode cand) = 0;
};

class Pattern
{
 public:
  /**********
   * Fields *
   **********/

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
   * i is in d_subPatPosns if and only if d_pat[i] has a matchable variable as a
   * proper subterm.
   */
  Positions d_subPatPosns;

  /**
   * i is in d_varPosns if and only if d_pat[i] is a matchable variable.
   */
  Positions d_varPosns;

  /**
   * i is in d_groundPosns if and only if d_pat[i] is not a matchable variable
   * and does not contain a matchable variable as a proper subterm.
   */
  Positions d_groundPosns;

  /**
   * i is in d_boundPosns if and only if this Pattern object has added a mapping
   * for d_pat[i] to its owner's d_subs.
   */
  Positions d_boundPosns;

  /**
   * Let `ematch` denote the EMatch object that owns this Pattern object.
   *
   * For all values of i between 0 and (d_subPatPosns.size() - 1), inclusive,
   * we require that ematch.d_subPats[d_subPatIdxs[i]] is a pointer to
   * the Pattern object for d_pat[d_subPatPosns[i]].
   */
  Indices d_subPatIdxs;

  /*************
   * Functions *
   *************/

  /* Pattern & helpers */
  Pattern(Node pat);

  void populateSubPatVarGroundPosns();
  /*********************/

  /* reset & helpers */
  void reset(const Node eqc, CandidateCallback* callback, EqualityEngine* ee);

  void populateCands(const Node eqc, CandidateCallback* callback, EqualityEngine* ee);

  bool checkGroundPosns(const Node term, EqualityEngine* ee);
  /*******************/

  /* next & helpers */
  MaybeJobs next(Subs& subs, EqualityEngine* ee);

  MaybePositionToNode getMappings(const Node cand, Subs& subs, EqualityEngine* ee);

  void commitMappings(const PositionToNode& mappings, Subs& subs);

  Jobs getNewJobs(const Node cand, EqualityEngine* ee);
  /******************/

  /* Other */
  void addChildren(Patterns& subPats);

  void backtrack(Subs& subs);

  static void debugPrintPosns(const Positions& posns, const TNode& term, ostream& out);
  /*********/
};

class EMatch
{
 public:
  EMatch(Node pat, CandidateCallback* callback, EqualityEngine* ee);

  /**
   * We want to produce substitutions `sigma` such that `sigma` applied to
   * `d_pat` is equivalent to `d_eqc`.  The image of `d_pat` under `sigma`
   * is not guaranteed to be in the equality engine.
   */
  Node d_pat;
  Node d_eqc;

  /**
   * We will not use members of `d_eqc` for which d_candCallback.consider()
   * returns false.
   */
  CandidateCallback* d_callback;

  EqualityEngine* d_ee;

  /**
   * The sub-patterns of `d_pat`.
   *
   * The i th sub-pattern of `d_pat` that appears in a left-to-right
   * breadth-first traversal of `d_pat` will be placed at index i.
   *
   * d_pat == d_subPats.at(0)
   */
  Patterns d_subPats;

  /**
   * d_cursor starts at 0 and is incremented when the matching task at
   * d_subPats[d_cursor] is successful.  When d_cursor equals d_subPats.size()
   * it means our e-matching attempt has succeeded.
   */
  size_t d_cursor;

  /**
   * The current substitution.
   */
  Subs d_subs;

  /**
   * Sets up this object to match `d_pat` with `eqc`.
   */
  void reset(Node eqc);

  /**
   * Returns an empty optional if and only if there are no more substitutions
   * that make `d_pat` equivalent to `d_eqc`.  Otherwise returns an optional
   * that contains a substitution `sigma` such that `sigma` applied to `d_pat`
   * is equivalent to `d_eqc`.
   */
  MaybeSubs next();

  void debugPrintState(ostream& out);

  void populateSubPats();
};
}  // namespace cvc5::internal

#endif /* CVC5__EXPR__E_MATCH_H */
