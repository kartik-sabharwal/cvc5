#include "theory/quantifiers/enumerative_conjecture_generator.h"

#include <sstream>
#include <unordered_map>
#include <unordered_set>

#include "cvc5_public.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "expr/subs.h"
#include "expr/sygus_grammar.h"
#include "theory/datatypes/sygus_datatype_utils.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
CVC5_UNUSED std::ostream& operator<<(std::ostream& out,
                                     std::vector<TypeNode>& vec)
{
  out << "{";
  std::vector<TypeNode>::iterator eltRef = vec.begin();
  const std::vector<TypeNode>::iterator eltMax = vec.end();
  if (eltRef != eltMax)
  {
    out << *eltRef;
    ++eltRef;
    for (; eltRef != eltMax; ++eltRef)
    {
      out << ", " << *eltRef;
    }
  }
  out << "}";
  return out;
}

CVC5_UNUSED std::ostream& operator<<(std::ostream& out,
                                     const Candidate& candidate)
{
  out << candidate.d_confirmed;
  return out;
}

bool operator<(const Candidate& c0, const Candidate& c1)
{
  return c0.d_confirmed < c1.d_confirmed;
}

EnumerativeConjectureGenerator::EnumerativeConjectureGenerator(
    Env& env,
    QuantifiersState& qs,
    QuantifiersInferenceManager& qim,
    QuantifiersRegistry& qr,
    TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr)
{
  d_nodeManager = nodeManager();
  d_rootType = d_nodeManager->mkSort("rootType");
  d_rootNonTerminal = NodeManager::mkBoundVar(d_rootType);
  d_maximumSize =
      options().quantifiers.enumerativeConjectureGeneratorMaximumSize;
  d_maximumDifference =
      options().quantifiers.enumerativeConjectureGeneratorMaximumDifference;
  d_clock = 0;
  d_period = options().quantifiers.enumerativeConjectureGeneratorPeriod;
  d_preferConstRepresentatives =
      options().quantifiers.preferConstRepresentatives;
  d_preferActiveTerms = options().quantifiers.preferActiveTerms;
}

EnumerativeConjectureGenerator::~EnumerativeConjectureGenerator() {}

bool EnumerativeConjectureGenerator::needsCheck(Theory::Effort e)
{
  return d_qstate.getInstWhenNeedsCheck(e);
}

void EnumerativeConjectureGenerator::reset_round(Theory::Effort) {}

void EnumerativeConjectureGenerator::updateClock(const QEffort qEffort,
                                                 size_t& clock,
                                                 const size_t period)
{
  if (qEffort == QEFFORT_STANDARD)
  {
    ++clock;

    clock %= period;
  }
}

bool EnumerativeConjectureGenerator::isSymbolRelevant(const TermDb* termDb,
                                                      const size_t i)
{
  TNode op = termDb->getOperator(i);

  const Kind kind = op.getKind();

  bool ctxtEnum = false;

  op.getAttribute(CtxtEnumAttribute(), ctxtEnum);

  return kind != Kind::APPLY_TESTER && kind != Kind::APPLY_SELECTOR
         && termDb->getNumGroundTerms(op) > 0 && !ctxtEnum;
}

std::vector<Node> EnumerativeConjectureGenerator::getRelevantFunctionSymbols(
    TermDb* termDatabase)
{
  /* Suppose we get the i th "operator" from the term database.  "operator" in
     this case means one of: uninterpreted function symbol, constructor symbol,
     application of tester symbol, or application of selector symbol.  We want
     to ignore the latter two and direct our attention to function symbols and
     constructor symbols.  A function symbol or a constructor symbol is
     *relevant* only if it appears in some ground term.

     This function returns a vector<TNode> and not a vector<Node> because the
     relevant function symbols and constructor symbols are "owned" by the term
     database. */

  std::vector<Node> result;

  for (size_t i = 0; i < termDatabase->getNumOperators(); ++i)
  {
    if (isSymbolRelevant(termDatabase, i))
    {
      result.push_back(termDatabase->getOperator(i));
    }
  }

  return result;
}

void EnumerativeConjectureGenerator::updateSymbolToKind(
    TermDb* termDatabase,
    const std::vector<Node>& functionSymbols,
    std::unordered_map<Node, Kind>& symbolToKind)
{
  for (std::vector<Node>::const_iterator symbolRef = functionSymbols.begin();
       symbolRef != functionSymbols.end();
       ++symbolRef)
  {
    Node symbol = *symbolRef;
    Node groundTerm = termDatabase->getGroundTerm(symbol, 0);
    symbolToKind[symbol] = groundTerm.getKind();
  }
}

std::vector<TypeNode> EnumerativeConjectureGenerator::getRelevantTypes(
    const std::vector<Node>& functionSymbols)
{
  std::unordered_set<TypeNode> types;

  for (std::vector<Node>::const_iterator symbolRef = functionSymbols.begin();
       symbolRef != functionSymbols.end();
       ++symbolRef)
  {
    Node symbol = *symbolRef;

    TypeNode symbolType = symbol.getType();

    for (TypeNode::const_iterator typeRef = symbolType.begin();
         typeRef != symbolType.end();
         ++typeRef)
    {
      types.insert(*typeRef);
    }
  }

  std::vector<TypeNode> result;

  result.insert(result.end(), types.begin(), types.end());

  return result;
}

void EnumerativeConjectureGenerator::updateTypeToIn(
    NodeManager* nodeManagerPtr,
    const std::vector<TypeNode>& types,
    const TypeNode rootType,
    std::unordered_map<TypeNode, Node>& typeToIn)
{
  SkolemManager* skolemManager = nodeManagerPtr->getSkolemManager();

  for (std::vector<TypeNode>::const_iterator typeRef = types.begin();
       typeRef != types.end();
       ++typeRef)
  {
    TypeNode type = *typeRef;

    if (!hasKey(typeToIn, type))
    {
      const TypeNode injectorType =
          nodeManagerPtr->mkFunctionType(type, rootType);

      std::stringstream injectorNameStream;
      injectorNameStream << "in" << type;
      const std::string injectorName = injectorNameStream.str();

      const Node injectorSymbol =
          skolemManager->mkDummySkolem(injectorName, injectorType);

      typeToIn[type] = injectorSymbol;
    }
  }
}

void EnumerativeConjectureGenerator::updateTypeToNonTerminal(
    const std::vector<TypeNode>& types,
    std::unordered_map<TypeNode, Node>& typeToNonTerminal)
{
  for (std::vector<TypeNode>::const_iterator typeRef = types.begin();
       typeRef != types.end();
       ++typeRef)
  {
    const TypeNode type = *typeRef;

    if (!hasKey(typeToNonTerminal, type))
    {
      const std::string name = (std::stringstream() << "nt" << type).str();

      const Node nonTerminal = NodeManager::mkBoundVar(name, type);

      typeToNonTerminal[type] = nonTerminal;
    }
  }
}

void EnumerativeConjectureGenerator::updateTypeToVariables(
    const std::vector<TypeNode>& types,
    expr::TermCanonize& termCanonize,
    const size_t maximumSize,
    std::unordered_map<TypeNode, std::vector<Node>>& typeToVariables)
{
  for (std::vector<TypeNode>::const_iterator typeRef = types.begin();
       typeRef != types.end();
       ++typeRef)
  {
    const TypeNode type = *typeRef;

    if (!hasKey(typeToVariables, type))
    {
      std::vector<Node>& variables = typeToVariables[type];

      for (size_t i = 0; i < maximumSize; ++i)
      {
        variables.push_back(termCanonize.getCanonicalFreeVar(type, i));
      }
    }
  }
}

std::vector<Node> EnumerativeConjectureGenerator::getNonTerminals(
    const TNode rootNonTerminal,
    const std::vector<TypeNode>& types,
    const std::unordered_map<TypeNode, Node>& typeToNonTerminal)
{
  std::vector<Node> result = {rootNonTerminal};

  for (std::vector<TypeNode>::const_iterator typeRef = types.begin();
       typeRef != types.end();
       ++typeRef)
  {
    result.push_back(typeToNonTerminal.at(*typeRef));
  }

  return result;
}

std::vector<std::pair<Node, Node>>
EnumerativeConjectureGenerator::getInjectorRules(
    NodeManager* nodeManagerPtr,
    const TNode rootNonTerminal,
    const std::vector<TypeNode>& types,
    const std::unordered_map<TypeNode, Node>& typeToNonTerminal,
    const std::unordered_map<TypeNode, Node>& typeToIn)
{
  std::vector<std::pair<Node, Node>> result;

  for (std::vector<TypeNode>::const_iterator typeRef = types.begin();
       typeRef != types.end();
       ++typeRef)
  {
    const TypeNode type = *typeRef;

    const Node nonTerminal = typeToNonTerminal.at(type);

    const Node injector = typeToIn.at(type);

    const Node rule = nodeManagerPtr->mkNode(
        Kind::APPLY_UF, std::vector<Node>{injector, nonTerminal});

    result.push_back(std::pair<Node, Node>{rootNonTerminal, rule});
  }

  return result;
}

std::vector<std::pair<Node, Node>>
EnumerativeConjectureGenerator::getFunctionRules(
    NodeManager* nodeManagerPtr,
    const std::vector<Node>& functionSymbols,
    const std::unordered_map<Node, Kind>& symbolToKind,
    const std::unordered_map<TypeNode, Node>& typeToNonTerminal)
{
  std::vector<std::pair<Node, Node>> result;

  for (std::vector<Node>::const_iterator symbolRef = functionSymbols.begin();
       symbolRef != functionSymbols.end();
       ++symbolRef)
  {
    const Node symbol = *symbolRef;

    const TypeNode type = symbol.getType();

    std::vector<Node> application = {symbol};

    const TypeNode::const_iterator rangeTypeRef = type.end() - 1;

    for (TypeNode::const_iterator domainTypeRef = type.begin();
         domainTypeRef != rangeTypeRef;
         ++domainTypeRef)
    {
      application.push_back(typeToNonTerminal.at(*domainTypeRef));
    }

    const Kind applicationKind = symbolToKind.at(symbol);

    const Node nonTerminal = typeToNonTerminal.at(*rangeTypeRef);

    const Node rule = nodeManagerPtr->mkNode(applicationKind, application);

    result.push_back(std::pair<Node, Node>{nonTerminal, rule});
  }

  return result;
}

std::vector<std::pair<Node, Node>>
EnumerativeConjectureGenerator::getVariableRules(
    const std::vector<TypeNode>& types,
    const std::unordered_map<TypeNode, Node>& typeToNonTerminal,
    const std::unordered_map<TypeNode, std::vector<Node>> typeToVariables)
{
  std::vector<std::pair<Node, Node>> result;

  for (std::vector<TypeNode>::const_iterator typeRef = types.begin();
       typeRef != types.end();
       ++typeRef)
  {
    const TypeNode type = *typeRef;

    const Node nonTerminal = typeToNonTerminal.at(type);

    const std::vector<Node>& variables = typeToVariables.at(type);

    for (std::vector<Node>::const_iterator variableRef = variables.begin();
         variableRef != variables.end();
         ++variableRef)
    {
      result.push_back(std::pair<Node, Node>{nonTerminal, *variableRef});
    }
  }

  return result;
}

TypeNode EnumerativeConjectureGenerator::getGrammarType(
    NodeManager* nodeManagerPtr,
    const TNode rootNonTerminal,
    const std::vector<Node>& functionSymbols,
    const std::unordered_map<Node, Kind>& symbolToKind,
    const std::vector<TypeNode>& types,
    const std::unordered_map<TypeNode, Node>& typeToNonTerminal,
    const std::unordered_map<TypeNode, Node>& typeToIn,
    const std::unordered_map<TypeNode, std::vector<Node>>& typeToVariables)
{
  const std::vector<Node> nonTerminals =
      getNonTerminals(rootNonTerminal, types, typeToNonTerminal);

  SygusGrammar grammar(std::vector<Node>(), nonTerminals);

  const std::vector<std::pair<Node, Node>> injectorRules = getInjectorRules(
      nodeManagerPtr, rootNonTerminal, types, typeToNonTerminal, typeToIn);

  const std::vector<std::pair<Node, Node>> functionRules = getFunctionRules(
      nodeManagerPtr, functionSymbols, symbolToKind, typeToNonTerminal);

  const std::vector<std::pair<Node, Node>> variableRules =
      getVariableRules(types, typeToNonTerminal, typeToVariables);

  std::vector<std::pair<Node, Node>> rules;
  rules.insert(rules.end(), injectorRules.begin(), injectorRules.end());
  rules.insert(rules.end(), functionRules.begin(), functionRules.end());
  rules.insert(rules.end(), variableRules.begin(), variableRules.end());

  for (std::vector<std::pair<Node, Node>>::const_iterator ruleRef =
           rules.begin();
       ruleRef != rules.end();
       ++ruleRef)
  {
    const std::pair<Node, Node>& rule = *ruleRef;

    grammar.addRule(std::get<0>(rule), std::get<1>(rule));
  }

  const TypeNode grammarType = grammar.resolve();

  return grammarType;
}

std::pair<std::vector<std::unordered_set<Node>>,
          std::unordered_map<Node, Index>>
EnumerativeConjectureGenerator::getEnumerationData(
    SygusTermEnumerator& termEnumerator,
    expr::TermCanonize& termCanonize,
    const size_t maximumSize)
{
  CVC5_UNUSED std::ostream& out = Trace("enumerative-conjecture-generator");

  std::vector<std::unordered_set<Node>> sizeToCanonicals;
  sizeToCanonicals.resize(maximumSize + 1);

  std::unordered_map<Node, Index> variableToIndex;

  Node term;

  do
  {
    term = termEnumerator.getCurrent();

    if (!term.isNull() && computeSize(term) <= maximumSize)
    {
      std::unordered_set<Node> variables;
      expr::getSubtermsKind(Kind::BOUND_VARIABLE, term, variables);

      std::unordered_set<Node> applications;
      expr::getSubtermsKind(Kind::APPLY_UF, term[0], applications, false);

      if (!variables.empty() && !applications.empty())
      {
        addTerm(termCanonize, term, variables, variableToIndex);

        const Node canonical =
            termCanonize.getCanonicalTerm(term, false, false);

        sizeToCanonicals[computeSize(canonical)].insert(canonical);
      }
    }
  } while (underestimateSize(term) <= maximumSize
           && termEnumerator.increment());

  return std::pair<std::vector<std::unordered_set<Node>>,
                   std::unordered_map<Node, Index>>{sizeToCanonicals,
                                                    variableToIndex};
}

std::unordered_map<Node, std::vector<Subs>>
EnumerativeConjectureGenerator::getCanonicalToSubstitutions(
    TermDb* termDatabase,
    eq::EqualityEngine* equalityEngine,
    const std::vector<std::unordered_set<Node>>& sizeToCanonicals,
    const bool preferConstRepresentatives,
    const bool preferActiveTerms)
{
  typedef std::unordered_map<Node, std::vector<Subs>> Result;

  Result result;

  for (size_t size = 0; size < sizeToCanonicals.size(); ++size)
  {
    const std::unordered_set<Node>& canonicals = sizeToCanonicals[size];

    typedef std::unordered_set<Node>::const_iterator NodePtr;

    for (NodePtr canonicalPtr = canonicals.begin();
         canonicalPtr != canonicals.end();
         ++canonicalPtr)
    {
      TNode lhs = (*canonicalPtr)[0];

      result[lhs] = findSubstitutions(termDatabase,
                                      equalityEngine,
                                      lhs,
                                      preferConstRepresentatives,
                                      preferActiveTerms);
    }
  }

  return result;
}

void EnumerativeConjectureGenerator::debugPrintSizeToCompatibles(
    std::ostream& out, TNode canonical, const Vector<Vector<Node>>& szToCompats)
{
  out << "LHS: " << canonical << std::endl;

  for (size_t sz = 0; sz < szToCompats.size(); ++sz)
  {
    out << "- Size: " << sz << std::endl;

    const Vector<Node>& compats = szToCompats[sz];

    for (size_t i = 0; i < compats.size(); ++i)
    {
      out << "- RHS: " << compats[i] << std::endl;
    }
  }
}

CandidateIndex EnumerativeConjectureGenerator::getCandidateIndex(
    const size_t maxSz,
    const size_t maxDiff,
    expr::TermCanonize& canonize,
    EntailmentCheck* entChk,
    eq::EqualityEngine* ee,
    const std::vector<std::unordered_set<Node>>& szToCanons,
    const std::unordered_map<Node, Index>& varToIdx,
    const std::unordered_map<Node, std::vector<Subs>>& lhsToSubss)
{
  CVC5_UNUSED std::ostream& out = Trace("enumerative-conjecture-generator");

  CandidateIndex result;
  result.resize(2 * maxSz + 1);

  for (size_t canonSz = 0; canonSz <= maxSz; ++canonSz)
  {
    const Set<Node>& canons = szToCanons[canonSz];

    for (CIt<Set<Node>> canon = canons.begin(); canon != canons.end(); ++canon)
    {
      TNode lhs = (*canon)[0];

      const Vector<Subs>& subss = lhsToSubss.at(lhs);

      const Vector<Vector<Node>> szToCompats =
          findCompatible(maxSz, maxDiff, varToIdx, canonize, *canon);

      for (size_t compatSz = 0; compatSz <= maxSz; ++compatSz)
      {
        const size_t candSz = canonSz + compatSz;

        PriorityQueue<Candidate>& cands = result[candSz];

        const Vector<Node>& compats = szToCompats[compatSz];

        for (CIt<Vector<Node>> compat = compats.begin();
             compat != compats.end();
             ++compat)
        {
          TNode rhs = (*compat)[0];

          if (lhs != rhs)
          {
            const Score score = getScore(entChk, ee, lhs, rhs, subss);

            const size_t tested = std::get<0>(score);

            const size_t confirmed = std::get<1>(score);

            if (tested > 0 && confirmed == tested)
            {
              cands.emplace(lhs, rhs, tested, confirmed);
            }
          }
        }
      }
    }
  }

  return result;
}

std::pair<size_t, size_t> EnumerativeConjectureGenerator::getScore(
    EntailmentCheck* entChk,
    const eq::EqualityEngine* ee,
    TNode lhs,
    TNode rhs,
    const Vector<Subs>& subss)
{
  size_t tested = 0;
  size_t confirmed = 0;

  for (CIt<Vector<Subs>> subs = subss.begin(); subs != subss.end(); ++subs)
  {
    TNode concrLhs = entChk->getEntailedTerm(subs->apply(lhs));
    TNode concrRhs = entChk->getEntailedTerm(subs->apply(rhs));

    if (!concrLhs.isNull() && !concrRhs.isNull())
    {
      ++tested;

      if (!ee->areDisequal(concrLhs, concrRhs, false))
      {
        ++confirmed;
      }
    }
  }

  return Score(tested, confirmed);
}

void EnumerativeConjectureGenerator::checkHelper()
{
  beginCallDebug();

  CVC5_UNUSED std::ostream& traceStream =
      Trace("enumerative-conjecture-generator");

  TermDb* termDatabase = getTermDatabase();

  NodeManager* nodeManagerPtr = nodeManager();

  d_relevantFunctionSymbols = getRelevantFunctionSymbols(termDatabase);

  d_relevantTypes = getRelevantTypes(d_relevantFunctionSymbols);

  updateSymbolToKind(termDatabase, d_relevantFunctionSymbols, d_symbolToKind);

  updateTypeToIn(nodeManagerPtr, d_relevantTypes, d_rootType, d_typeToIn);

  updateTypeToNonTerminal(d_relevantTypes, d_typeToNonTerminal);

  updateTypeToVariables(
      d_relevantTypes, d_termCanonize, d_maximumSize, d_typeToVariables);

  const TypeNode grammarType = getGrammarType(nodeManagerPtr,
                                              d_rootNonTerminal,
                                              d_relevantFunctionSymbols,
                                              d_symbolToKind,
                                              d_relevantTypes,
                                              d_typeToNonTerminal,
                                              d_typeToIn,
                                              d_typeToVariables);

  SygusTermEnumerator sygusTermEnumerator =
      SygusTermEnumerator(d_env, grammarType, nullptr, false, 0);

  std::pair<std::vector<std::unordered_set<Node>>,
            std::unordered_map<Node, Index>>
      enumerationData = getEnumerationData(
          sygusTermEnumerator, d_termCanonize, d_maximumSize);

  std::vector<std::unordered_set<Node>>& sizeToCanonicals =
      std::get<0>(enumerationData);

  CVC5_UNUSED std::unordered_map<Node, Index>& variableToIndex =
      std::get<1>(enumerationData);

  Map<Node, Vector<Subs>> lhsToSubss =
      getCanonicalToSubstitutions(termDatabase,
                                  getEqualityEngine(),
                                  sizeToCanonicals,
                                  d_preferConstRepresentatives,
                                  d_preferActiveTerms);

  CandidateIndex candIdx = getCandidateIndex(d_maximumSize,
                                             d_maximumDifference,
                                             d_termCanonize,
                                             d_treg.getEntailmentCheck(),
                                             getEqualityEngine(),
                                             sizeToCanonicals,
                                             variableToIndex,
                                             lhsToSubss);

  debugPrintCandidateIndex(traceStream, candIdx);

  endCallDebug();
}

void EnumerativeConjectureGenerator::debugPrintLHSToSubstitutions(
    std::ostream& out,
    const Vector<Set<Node>>& szToCanons,
    const Map<Node, Vector<Subs>>& lhsToSubss)
{
  for (size_t sz = 0; sz < szToCanons.size(); ++sz)
  {
    out << "Size " << sz << ":" << std::endl;

    const Set<Node>& canons = szToCanons[sz];

    for (CIt<Set<Node>> canon = canons.begin(); canon != canons.end(); ++canon)
    {
      TNode lhs = (*canon)[0];

      out << "- LHS " << lhs << ":" << std::endl;

      if (hasKey(lhsToSubss, lhs))
      {
        const Vector<Subs>& subss = lhsToSubss.at(lhs);

        for (CIt<Vector<Subs>> subs = subss.begin(); subs != subss.end();
             ++subs)
        {
          out << "-- Substitution " << *subs << std::endl;
        }
      }
      else
      {
        out << "...no substitutions found!" << std::endl;
      }
    }
  }
}

void EnumerativeConjectureGenerator::debugPrintCandidateIndex(
    std::ostream& out, const Vector<PriorityQueue<Candidate>>& candIdx)
{
  for (size_t candSz = 0; candSz < candIdx.size(); ++candSz)
  {
    out << "Candidate size " << candSz << ":" << std::endl;

    // In theory this should copy the queue candIdx[candSz] to cands so we can
    // freely remove elements from cands without modifying candIdx.
    PriorityQueue<Candidate> cands = candIdx[candSz];

    while (!cands.empty())
    {
      const Candidate& cand = cands.top();

      out << "* " << cand.d_left << " = " << cand.d_right << ", "
          << cand.d_confirmed << "/" << cand.d_tested << " confirmed"
          << std::endl;

      cands.pop();
    }
  }
}

void EnumerativeConjectureGenerator::check(CVC5_UNUSED Theory::Effort effort,
                                           QEffort qEffort)
{
  updateClock(qEffort, d_clock, d_period);

  if (d_clock == 0)
  {
    checkHelper();
  }
}

size_t EnumerativeConjectureGenerator::underestimateSize(TNode n)
{
  struct Job
  {
    Node d_out;
  };

  std::vector<Job*> jobs = {new Job{n}};

  size_t result = 0;

  while (!jobs.empty())
  {
    const Job* currentJob = jobs.back();

    jobs.pop_back();

    const Node currentN = currentJob->d_out;

    if (!currentN.isNull())
    {
      const Kind nKind = currentN.getKind();

      if (nKind == Kind::APPLY_CONSTRUCTOR || nKind == Kind::APPLY_UF)
      {
        Node::iterator childRef = currentN.begin();

        const Node::iterator childRefMax = currentN.end();

        if (childRef != childRefMax)
        {
          ++result;

          for (; childRef != childRefMax; ++childRef)
          {
            jobs.push_back(new Job{*childRef});
          }
        }
      }
    }

    delete currentJob;
  }

  return result;
}

size_t EnumerativeConjectureGenerator::computeSize(TNode n)
{
  struct Job
  {
    Node d_out;
  };

  std::vector<Job*> jobs{new Job{n}};

  size_t result = 0;

  std::unordered_set<Node> seen;

  while (!jobs.empty())
  {
    const Job* job = jobs.back();

    jobs.pop_back();

    const Node node = job->d_out;

    if (!node.isNull())
    {
      const Kind kind = node.getKind();

      if (kind == Kind::BOUND_VARIABLE && member(seen, node))
      {
        ++result;
      }
      else if (kind == Kind::BOUND_VARIABLE)
      {
        seen.insert(node);
      }
      else if (kind == Kind::APPLY_CONSTRUCTOR || kind == Kind::APPLY_UF)
      {
        ++result;

        for (Node::iterator childPtr = node.begin(); childPtr != node.end();
             ++childPtr)
        {
          jobs.emplace_back(new Job{*childPtr});
        }
      }
    }

    delete job;
  }

  return result;
}

std::string EnumerativeConjectureGenerator::identify() const
{
  return "enumerative-conjecture-generator";
}

void EnumerativeConjectureGenerator::addTerm(
    expr::TermCanonize& termCanonize,
    const Node term,
    const std::unordered_set<Node>& variableSet,
    std::unordered_map<Node, Index>& rootVariableToIndex)
{
  /* To implement this function we do the following:
   *
   * - collect the bound variables in `term` in a vector,
   * - sort the vector in increasing order of canonical variable index,
   * - go deeper in d_variableToIndex according to the sorted vector,
   * - when you're at the end of the vector add the term to d_terms.
   */
  std::vector<Node> variables;
  variables.insert(variables.end(), variableSet.begin(), variableSet.end());

  std::sort(
      variables.begin(), variables.end(), [termCanonize](TNode n0, TNode n1) {
        return termCanonize.getIndexForFreeVariable(n0)
               < termCanonize.getIndexForFreeVariable(n1);
      });

  std::vector<Node>::const_iterator variableRef = variables.begin();

  Index* indexPtr = &rootVariableToIndex[*variableRef];

  ++variableRef;

  for (; variableRef != variables.end(); ++variableRef)
  {
    indexPtr = &(indexPtr->d_variableToIndex[*variableRef]);
  }

  indexPtr->d_terms.push_back(term);
}

void EnumerativeConjectureGenerator::debugPrintSizeToCanonicals(
    std::ostream& out,
    const size_t maximumSize,
    const std::vector<std::unordered_set<Node>>& sizeToCanonicals)
{
  for (size_t size = 0; size <= maximumSize; ++size)
  {
    out << "Canonical terms sized " << size << ":" << std::endl;

    const std::unordered_set<Node>& canonicals = sizeToCanonicals[size];
    for (std::unordered_set<Node>::const_iterator termPtr = canonicals.begin();
         termPtr != canonicals.end();
         ++termPtr)
    {
      out << "- " << *termPtr << std::endl;
    }
  }
}

void EnumerativeConjectureGenerator::debugPrintIndex(
    std::ostream& out,
    const std::unordered_map<Node, Index>& rootVariableToIndex)
{
  struct Job
  {
    std::vector<Node> d_path;
    const Index* d_index;
  };

  std::vector<Job*> jobs;

  for (std::unordered_map<Node, Index>::const_iterator entryPtr =
           rootVariableToIndex.begin();
       entryPtr != rootVariableToIndex.end();
       ++entryPtr)
  {
#define ENTRY *entryPtr
    jobs.emplace_back(
        new Job{std::vector<Node>{std::get<0>(ENTRY)}, &std::get<1>(ENTRY)});
#undef ENTRY
  }

  while (!jobs.empty())
  {
    Job* job = jobs.back();
    jobs.pop_back();

    std::vector<Node>& path = job->d_path;
    const Index* index = job->d_index;
    const std::unordered_map<Node, Index>& variableToIndex =
        index->d_variableToIndex;

    out << "Path " << path << ":" << std::endl;
    out << "Terms " << index->d_terms << std::endl;

    for (std::unordered_map<Node, Index>::const_iterator entryPtr =
             variableToIndex.begin();
         entryPtr != variableToIndex.end();
         ++entryPtr)
    {
#define ENTRY *entryPtr
      std::vector<Node> branchPath;
      branchPath.insert(branchPath.end(), path.begin(), path.end());
      branchPath.push_back(std::get<0>(ENTRY));

      jobs.emplace_back(new Job{branchPath, &std::get<1>(ENTRY)});
#undef ENTRY
    }

    delete job;
  }
}

bool EnumerativeConjectureGenerator::variableLessThan(
    const expr::TermCanonize& termCanonize, TNode n0, TNode n1)
{
  return termCanonize.getIndexForFreeVariable(n0)
         < termCanonize.getIndexForFreeVariable(n1);
}

std::vector<Node> EnumerativeConjectureGenerator::getSortedVariables(
    const expr::TermCanonize& termCanonize, TNode term)
{
  Set<Node> variables;

  expr::getSubtermsKind(Kind::BOUND_VARIABLE, term, variables);

  Vector<Node> result(variables.cbegin(), variables.cend());

  std::sort(result.begin(), result.end(), [termCanonize](TNode n0, TNode n1) {
    return variableLessThan(termCanonize, n0, n1);
  });

  return result;
}

std::vector<std::vector<Node>> EnumerativeConjectureGenerator::findCompatible(
    const size_t maximumSize,
    const size_t maximumDifference,
    const Map<Node, Index>& rootVariableToIndex,
    expr::TermCanonize& termCanonize,
    TNode canonical)
{
  Vector<Vector<Node>> result;

  result.resize(maximumSize + 1);

  const Vector<Node> variables = getSortedVariables(termCanonize, canonical);

  const size_t nVariables = variables.size();

  class Job
  {
   public:
    size_t d_position;
    Ref<const Index> d_index;
    size_t d_skipped;
    size_t d_difference;

    Job(const size_t position,
        const Index& index,
        const size_t skipped,
        const size_t difference)
        : d_position(position),
          d_index(std::cref(index)),
          d_skipped(skipped),
          d_difference(difference)
    {
    }
  };

  Vector<Ptr<Job>> jobs;

  for (size_t position = 0; position < nVariables; ++position)
  {
    TNode variable = variables[position];

    if (hasKey(rootVariableToIndex, variable))
    {
      jobs.emplace_back(new Job(position + 1,
                                rootVariableToIndex.at(variable),
                                position,
                                nVariables - 1));
    }
  }

  while (!jobs.empty())
  {
    Ptr<Job> job = std::move(jobs.back());

    jobs.pop_back();

    const size_t jPosition = job->d_position;
    const Index& jIndex = job->d_index.get();
    const size_t jSkipped = job->d_skipped;
    const size_t jDifference = job->d_difference;

    if (jDifference <= maximumDifference)
    {
      const Vector<Node>& jTerms = jIndex.d_terms;

      for (CIt<Vector<Node>> jTerm = jTerms.begin(); jTerm != jTerms.end();
           ++jTerm)
      {
        result[computeSize(*jTerm)].push_back(*jTerm);
      }
    }

    if (jSkipped <= maximumDifference)
    {
      const Map<Node, Index>& jVarToIdx = jIndex.d_variableToIndex;

      for (size_t position = jPosition; position < nVariables; ++position)
      {
        TNode variable = variables[position];

        if (hasKey(jVarToIdx, variable))
        {
          jobs.emplace_back(new Job(position + 1,
                                    jVarToIdx.at(variable),
                                    jSkipped + (position - jPosition),
                                    jDifference - 1));
        }
      }
    }
  }

  return result;
}

std::vector<std::vector<Node>>
EnumerativeConjectureGenerator::oldFindCompatible(TNode lhs)
{
  std::vector<std::vector<Node>> sizeToCompatible;

  sizeToCompatible.resize(d_maximumSize + 1);

  std::unordered_set<Node> variableSet;

  expr::getSubtermsKind(Kind::BOUND_VARIABLE, lhs, variableSet);

  const size_t variableCount = variableSet.size();

  std::vector<Node> variables;

  variables.insert(variables.end(), variableSet.begin(), variableSet.end());

  std::sort(variables.begin(), variables.end(), [this](Node n0, Node n1) {
    return this->d_termCanonize.getIndexForFreeVariable(n0)
           < this->d_termCanonize.getIndexForFreeVariable(n1);
  });

  struct Job
  {
    size_t d_position;
    Index* d_index;
    size_t d_skipped;
    size_t d_difference;
  };

  std::vector<Job*> jobs;

  for (size_t position = 0; position < variableCount; ++position)
  {
    Node variable = variables[position];

    if (hasKey(d_variableToIndex, variable))
    {
      jobs.push_back(new Job{position + 1,
                             &d_variableToIndex[variable],
                             position,
                             variableCount - 1});
    }
  }

  while (!jobs.empty())
  {
    Job* job = jobs.back();

    jobs.pop_back();

    size_t jobPosition = job->d_position;
    Index* jobIndex = job->d_index;
    size_t jobSkipped = job->d_skipped;
    size_t jobDifference = job->d_difference;

    if (jobSkipped <= d_maximumDifference)
    {
      if (jobDifference <= d_maximumDifference)
      {
        std::vector<Node>& jobTerms = jobIndex->d_terms;

        for (std::vector<Node>::const_iterator termRef = jobTerms.begin();
             termRef != jobTerms.end();
             ++termRef)
        {
          Node term = *termRef;

          const size_t termSize = computeSize(term);

          sizeToCompatible[termSize].push_back(term);
        }
      }

      std::unordered_map<Node, Index>& jobVariableToIndex =
          jobIndex->d_variableToIndex;

      for (size_t position = jobPosition; position < variableCount; ++position)
      {
        Node variable = variables[position];

        if (hasKey(jobVariableToIndex, variable))
        {
          jobs.push_back(new Job{position + 1,
                                 &jobVariableToIndex[variable],
                                 jobSkipped + position - jobPosition,
                                 jobDifference - 1});
        }
      }
    }

    delete job;
  }

  return sizeToCompatible;
}

TypeNode EnumerativeConjectureGenerator::findTypeByName(
    const std::string& name, const std::vector<TypeNode>& types)
{
  typedef std::vector<TypeNode>::const_iterator TypePtr;

  TypeNode result = TypeNode::null();

  TypePtr typePtr =
      std::find_if(types.begin(), types.end(), [name](const TypeNode& type) {
        return name.compare((std::stringstream() << type).str()) == 0;
      });

  if (typePtr != types.end())
  {
    result = *typePtr;
  }

  return result;
}

Node EnumerativeConjectureGenerator::findFunctionSymbolByName(
    const std::string& name, const std::vector<Node>& symbols)
{
  typedef std::vector<Node>::const_iterator SymbolPtr;

  Node result = Node::null();

  SymbolPtr symbolPtr =
      std::find_if(symbols.begin(), symbols.end(), [name](TNode symbol) {
        return symbol.getName() == name;
      });

  if (symbolPtr != symbols.end())
  {
    result = *symbolPtr;
  }

  return result;
}

std::vector<Subs> EnumerativeConjectureGenerator::findSubstitutions(
    TermDb* termDatabase,
    eq::EqualityEngine* equalityEngine,
    TNode canonical,
    const bool preferConstRepresentatives,
    const bool preferActiveTerms)
{
#define IMPLIES(implicant, implicand) (!(implicant) || (implicand))

  std::vector<Subs> substitutions;
  std::vector<Node> preferredClasses;

  typedef std::vector<Node>::const_iterator ReprPtr;

  for (eq::EqClassesIterator reprPtr = eq::EqClassesIterator(equalityEngine);
       !reprPtr.isFinished();
       ++reprPtr)
  {
    const Node repr = *reprPtr;

    if (repr.getType() == canonical.getType()
        && IMPLIES(preferConstRepresentatives, repr.isConst()))
    {
      preferredClasses.push_back(repr);
    }
  }

  for (ReprPtr reprPtr = preferredClasses.begin();
       reprPtr != preferredClasses.end();
       ++reprPtr)
  {
    Trail decisionQueue;
    decisionQueue.emplace_back(new Decision(termDatabase,
                                            equalityEngine,
                                            canonical,
                                            *reprPtr,
                                            preferConstRepresentatives,
                                            preferActiveTerms));

    size_t virtualBegin = 0;

    Subs substitution;

    while (!decisionQueue.empty() && virtualBegin <= decisionQueue.size()
           && IMPLIES(virtualBegin < decisionQueue.size()
                          && decisionQueue[virtualBegin]->isFinished(),
                      virtualBegin > 0))
    {
      if (virtualBegin == decisionQueue.size())
      {
        // virtualBegin > 0 because decisionQueue.size() > 0

        substitutions.push_back(substitution);

        --virtualBegin;

        decisionQueue[virtualBegin]->pop(substitution);
      }
      else if (decisionQueue[virtualBegin]->isFinished())
      {
        // virtualBegin > 0 because of all three: loop guard, virtualBegin !=
        // decisionQueue.size(), and decisionQueue[virtualBegin]->isFinished()

        for (size_t i = 0; i < decisionQueue.size() - virtualBegin; ++i)
        {
          delete decisionQueue.back();
          decisionQueue.pop_back();
        }

        --virtualBegin;

        decisionQueue[virtualBegin]->pop(substitution);
      }
      else if (decisionQueue[virtualBegin]->push(
                   termDatabase, equalityEngine, substitution, decisionQueue))
      {
        ++virtualBegin;
      }
      else
      {
        decisionQueue[virtualBegin]->pop(substitution);
      }
    }
  }

  return substitutions;
#undef IMPLIES
}

Decision::Decision(TermDb* termDatabase,
                   eq::EqualityEngine* equalityEngine,
                   TNode pattern,
                   TNode representative,
                   bool preferConstRepresentatives,
                   bool preferActiveTerms)
{
  d_pattern = pattern;
  d_nextCandidatePosition = 0;
  d_preferConstRepresentatives = preferConstRepresentatives;
  d_preferActiveTerms = preferActiveTerms;

  std::unordered_map<size_t, Node> positionToGround;

  for (size_t position = 0; position < d_pattern.getNumChildren(); ++position)
  {
    Node child = d_pattern[position];

    if (child.getKind() == Kind::BOUND_VARIABLE)
    {
      d_variablePositions.push_back(position);
    }
    else if (expr::hasBoundVar(child))
    {
      d_nonvariablePatternPositions.push_back(position);
    }
    else
    {
      if (equalityEngine->hasTerm(child))
      {
        positionToGround[position] = equalityEngine->getRepresentative(child);
      }
      else
      {
        positionToGround[position] = child;
      }
    }
  }

  Node patternHead = d_pattern.getOperator();

  for (eq::EqClassIterator memberRef =
           eq::EqClassIterator(representative, equalityEngine);
       !memberRef.isFinished();
       ++memberRef)
  {
    Node member = *memberRef;

    bool addMemberToCandidates = true;

    if (member.hasOperator() && member.getOperator() == patternHead
        && (!d_preferActiveTerms || termDatabase->isTermActive(member)))
    {
      for (std::unordered_map<size_t, Node>::const_iterator entryRef =
               positionToGround.begin();
           entryRef != positionToGround.end();
           ++entryRef)
      {
        const std::pair<size_t, Node>& entry = *entryRef;

        TNode memberGroundChild = member[std::get<0>(entry)];

        TNode patternGroundChild = std::get<1>(entry);

        addMemberToCandidates =
            addMemberToCandidates && memberGroundChild == patternGroundChild;
      }
    }
    else
    {
      addMemberToCandidates = false;
    }

    if (addMemberToCandidates)
    {
      d_candidates.push_back(member);
    }
  }
}

Node Decision::getPattern() { return d_pattern; }

bool Decision::push(TermDb* termDatabase,
                    eq::EqualityEngine* equalityEngine,
                    Subs& substitution,
                    Trail& decisionQueue)
{
  if (isFinished())
  {
    return false;
  }

  Node candidate = d_candidates[d_nextCandidatePosition];

  ++d_nextCandidatePosition;

  std::vector<Node> representatives;

  for (std::vector<size_t>::const_iterator positionRef =
           d_variablePositions.begin();
       positionRef != d_variablePositions.end();
       ++positionRef)
  {
    size_t position = *positionRef;

    Node variable = d_pattern[position];

    Node desiredImage = candidate[position];

    if (substitution.contains(variable))
    {
      Node image = substitution.getSubs(variable);

      if (equalityEngine->areEqual(image, desiredImage))
      {
        continue;
      }
      else
      {
        return false;
      }
    }
    else
    {
      substitution.add(variable, desiredImage);

      d_boundPositions.insert(position);
    }
  }

  for (std::vector<size_t>::const_iterator positionRef =
           d_nonvariablePatternPositions.begin();
       positionRef != d_nonvariablePatternPositions.end();
       ++positionRef)
  {
    Node representative =
        equalityEngine->getRepresentative(candidate[*positionRef]);

    if (!d_preferConstRepresentatives || representative.isConst())
    {
      representatives.push_back(representative);
    }
    else
    {
      return false;
    }
  }

  for (size_t i = 0; i < d_nonvariablePatternPositions.size(); ++i)
  {
    size_t childPosition = d_nonvariablePatternPositions[i];
    Node childPattern = d_pattern[childPosition];
    Node childRepresentative = representatives[i];

    decisionQueue.emplace_back(new Decision(termDatabase,
                                            equalityEngine,
                                            childPattern,
                                            childRepresentative,
                                            d_preferConstRepresentatives,
                                            d_preferActiveTerms));
  }

  return true;
}

void Decision::pop(Subs& substitution)
{
  for (std::unordered_set<size_t>::const_iterator boundPositionRef =
           d_boundPositions.begin();
       boundPositionRef != d_boundPositions.end();
       ++boundPositionRef)
  {
    substitution.erase(d_pattern[*boundPositionRef]);
  }

  d_boundPositions.clear();
}

bool Decision::isFinished()
{
  return d_nextCandidatePosition >= d_candidates.size();
}

Candidate::Candidate(TNode left,
                     TNode right,
                     const size_t tested,
                     const size_t confirmed)
    : d_left(left), d_right(right), d_tested(tested), d_confirmed(confirmed)
{
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
