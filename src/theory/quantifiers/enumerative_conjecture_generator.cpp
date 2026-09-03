#include "theory/quantifiers/enumerative_conjecture_generator.h"

#include <sstream>
#include <unordered_map>
#include <unordered_set>

#include "cvc5_public.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "expr/subs.h"
#include "expr/sygus_grammar.h"
#include "smt/set_defaults.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"

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

std::ostream& operator<<(std::ostream& out,
                         EnumerativeConjectureGenerator::FilterResult result)
{
  switch (result)
  {
    case EnumerativeConjectureGenerator::TRIVIAL:
    {
      out << "TRIVIAL";
      break;
    }
    case EnumerativeConjectureGenerator::CACHED:
    {
      out << "CACHED";
      break;
    }
    case EnumerativeConjectureGenerator::DEDUCTIVE:
    {
      out << "DEDUCTIVE";
      break;
    }
    case EnumerativeConjectureGenerator::INDUCTIVE:
    {
      out << "INDUCTIVE";
      break;
    }
    case EnumerativeConjectureGenerator::NONE:
    {
      out << "NONE";
      break;
    }
    default:
    {
      out << "impossible!";
      break;
    }
  }

  return out;
}

bool operator<(const Candidate& c0, const Candidate& c1)
{
  return c0.d_confirmed < c1.d_confirmed;
}

bool implies(const bool implicant, const std::function<bool()>& implicand)
{
  bool result = true;

  if (implicant)
  {
    result = implicand();
  }

  return result;
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
  d_clock = 1;
  d_period = options().quantifiers.enumerativeConjectureGeneratorPeriod;
  d_preferConstRepresentatives =
      options().quantifiers.preferConstRepresentatives;
  d_preferActiveTerms = options().quantifiers.preferActiveTerms;
  d_split = options().quantifiers.ecgSplit;
  d_defaultOptions.copyValues(options());
  d_defaultOptions.write_quantifiers().quantInduction = false;
  d_defaultOptions.write_quantifiers().dtStcInduction = false;
  d_defaultOptions.write_quantifiers().conjectureGen = false;
  d_defaultOptions.write_quantifiers().enumerativeConjectureGenerator = false;
  d_defaultOptions.write_quantifiers().contextualEnumerator = false;
  d_defaultOptions.write_quantifiers().quantSubCbqi = false;
}

EnumerativeConjectureGenerator::~EnumerativeConjectureGenerator() {}

bool EnumerativeConjectureGenerator::needsCheck(Theory::Effort e)
{
  return d_qstate.getInstWhenNeedsCheck(e);
}

void EnumerativeConjectureGenerator::reset_round(Theory::Effort) {}

void EnumerativeConjectureGenerator::updateClock(size_t& clock, const size_t period)
{
  clock = (clock + 1) % period;
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
    CVC5_UNUSED const size_t maximumSize,
    const size_t varsPerType,
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

      for (size_t i = 0; i < varsPerType; ++i)
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
    const Map<TypeNode, std::uint8_t>& typeToNumber,
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
        addTerm(termCanonize, typeToNumber, term, variableToIndex);

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
    const bool preferActiveTerms,
    const std::int64_t substitutionLimit)
{
  Map<Node, Vector<Subs>> result;

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
                                      preferActiveTerms,
                                      substitutionLimit);
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
    const Vector<Set<Node>>& szToCanons,
    const Map<Node, Index>& varToIdx,
    const Map<TypeNode, std::uint8_t>& typeToNumber,
    const Map<Node, Vector<Subs>>& lhsToSubss,
    NodeManager* nodeMgr,
    const Set<Node>& dedEnt,
    const Set<Node>& indEnt)
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

      const Vector<Vector<Node>> szToCompats = findCompatible(
          maxSz, maxDiff, varToIdx, canonize, typeToNumber, *canon);

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

          const Score score =
              getScore(entChk, ee, lhs, rhs, subss, nodeMgr, dedEnt, indEnt);

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

  return result;
}

std::pair<size_t, size_t> EnumerativeConjectureGenerator::getScore(
    EntailmentCheck* entChk,
    const eq::EqualityEngine* ee,
    TNode lhs,
    TNode rhs,
    const Vector<Subs>& subss,
    NodeManager* nodeMgr,
    const Set<Node>& dedEnt,
    const Set<Node>& indEnt)
{
  size_t tested = 0;
  size_t confirmed = 0;

  Node conj =
      candidateToConjecture(nodeMgr, Candidate(lhs, rhs, 0, 0), nullptr);

  if (lhs == rhs || member(dedEnt, conj) || member(indEnt, conj))
  {
    tested = 1;
    confirmed = 1;
  }
  else
  {
    CIt<Vector<Subs>> subs = subss.begin();

    while (tested == confirmed && subs != subss.end())
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

      ++subs;
    }
  }

  return Score(tested, confirmed);
}

bool EnumerativeConjectureGenerator::areSame(const Vector<Node>& v,
                                             const Vector<Node>& w)
{
  bool result = v.size() == w.size();

  CIt<Vector<Node>> sym = v.begin();

  while (result && sym != v.end())
  {
    result = member(w, *sym);

    ++sym;
  }

  return result;
}

void EnumerativeConjectureGenerator::updateTypeToNumber(
    const Vector<TypeNode>& types, Map<TypeNode, std::uint8_t>& typeToNum)
{
  for (CIt<Vector<TypeNode>> type = types.begin(); type != types.end(); ++type)
  {
    if (!hasKey(typeToNum, *type))
    {
      typeToNum[*type] = typeToNum.size();
    }
  }
}

void EnumerativeConjectureGenerator::checkHelper()
{
  CVC5_UNUSED std::ostream& traceStream =
      Trace("enumerative-conjecture-generator");

  TermDb* termDatabase = getTermDatabase();

  NodeManager* nodeMgr = nodeManager();

  Vector<Node> rlvFuncSyms = getRelevantFunctionSymbols(termDatabase);

  if (!areSame(d_relevantFunctionSymbols, rlvFuncSyms))
  {
    traceStream << "Relevant functions have changed!" << std::endl;

    d_relevantFunctionSymbols = rlvFuncSyms;

    d_relevantTypes = getRelevantTypes(d_relevantFunctionSymbols);

    updateSymbolToKind(termDatabase, d_relevantFunctionSymbols, d_symbolToKind);

    updateTypeToNumber(d_relevantTypes, d_typeToNumber);

    updateTypeToIn(nodeMgr, d_relevantTypes, d_rootType, d_typeToIn);

    updateTypeToNonTerminal(d_relevantTypes, d_typeToNonTerminal);

    updateTypeToVariables(d_relevantTypes,
                          d_termCanonize,
                          d_maximumSize,
                          options().quantifiers.ecgVarsPerType,
                          d_typeToVariables);

    const TypeNode grammarType = getGrammarType(nodeMgr,
                                                d_rootNonTerminal,
                                                d_relevantFunctionSymbols,
                                                d_symbolToKind,
                                                d_relevantTypes,
                                                d_typeToNonTerminal,
                                                d_typeToIn,
                                                d_typeToVariables);

    SygusTermEnumerator sygusTermEnumerator =
        SygusTermEnumerator(d_env, grammarType, nullptr, false, 0);

    Pair<Vector<Set<Node>>, Map<Node, Index>> enumerationData =
        getEnumerationData(
            sygusTermEnumerator, d_termCanonize, d_typeToNumber, d_maximumSize);

    d_sizeToCanonicals = std::get<0>(enumerationData);

    d_variableToIndex = std::get<1>(enumerationData);
  }

  const Map<Node, Vector<Subs>> lhsToSubss =
      getCanonicalToSubstitutions(termDatabase,
                                  getEqualityEngine(),
                                  d_sizeToCanonicals,
                                  d_preferConstRepresentatives,
                                  d_preferActiveTerms,
                                  options().quantifiers.ecgSubstitutionLimit);

  CandidateIndex candIdx = getCandidateIndex(d_maximumSize,
                                             d_maximumDifference,
                                             d_termCanonize,
                                             d_treg.getEntailmentCheck(),
                                             getEqualityEngine(),
                                             d_sizeToCanonicals,
                                             d_variableToIndex,
                                             d_typeToNumber,
                                             lhsToSubss,
                                             nodeManager(),
                                             d_deductivelyEntailed,
                                             d_inductivelyEntailed);

  // debugPrintCandidateIndex(traceStream, candIdx);

  filterCandidates(d_env,
                   d_defaultOptions,
                   d_qim,
                   d_treg,
                   nodeManager(),
                   options().quantifiers.ecgConjecturesPerRound,
                   d_inductivelyEntailed,
                   d_deductivelyEntailed,
                   options().quantifiers.ecgSubsolverTimeout,
                   *d_initialFacts,
                   candIdx,
                   d_conjectures,
                   d_qstate,
                   d_split);
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

void EnumerativeConjectureGenerator::debugPrintFacts(std::ostream& out,
                                                     const Set<TNode>& facts)
{
  out << "Facts:" << std::endl;

  for (CIt<Set<TNode>> fact = facts.begin(); fact != facts.end(); ++fact)
  {
    out << "* " << *fact << std::endl;
  }
}

std::unordered_set<TNode> EnumerativeConjectureGenerator::getInitialFacts(
    Valuation& valuation, quantifiers::TermRegistry& termReg)
{
  CVC5_UNUSED std::ostream& out = Trace("enumerative-conjecture-generator");

  Set<TNode> result;

  for (CIt<context::CDList<Assertion>> assertion =
           valuation.factsBegin(THEORY_UF);
       assertion != valuation.factsEnd(THEORY_UF);
       ++assertion)
  {
    if (valuation.isSatLiteral(*assertion) && valuation.isFixed(*assertion))
    {
      Set<Node> skolems;

      expr::getSubtermsKind(Kind::SKOLEM, *assertion, skolems, false);

      if (skolems.empty())
      {
        result.insert(*assertion);
      }
    }
  }

  quantifiers::FirstOrderModel* model = termReg.getModel();

  for (size_t i = 0; i < model->getNumAssertedQuantifiers(); ++i)
  {
    const Node phi = model->getAssertedQuantifier(i);

    const bool satLiteral = valuation.isSatLiteral(phi);
    const bool fixed = satLiteral && valuation.isFixed(phi);

    if (satLiteral && fixed)
    {
      result.insert(phi);
    }
    else if (satLiteral)
    {
      // out << "! sat literal " << phi
      //     << " is not an initial fact because it is not fixed" << std::endl;
    }
    else
    {
      // out << "! " << phi
      //     << " is not an initial fact because it is not a sat literal"
      //     << std::endl;
    }
  }

  return result;
}

std::unordered_set<TNode> EnumerativeConjectureGenerator::getProvedConjectures(
    const Set<TNode>& conjectures,
    const Valuation& valuation,
    const quantifiers::TermRegistry& termReg)
{
  std::ostream& out = Trace("enumerative-conjecture-generator");

  out << "getProvedConjectures current conjectures:" << std::endl;
  for (CIt<Set<TNode>> conjIter = conjectures.begin(); conjIter != conjectures.end(); ++conjIter)
  {
    out << "* " << *conjIter << std::endl;
  }

  Set<TNode> result;

  quantifiers::FirstOrderModel* model = termReg.getModel();

  for (size_t i = 0; i < model->getNumAssertedQuantifiers(); ++i)
  {
    const Node phi = model->getAssertedQuantifier(i);

    // valuation.isSatLiteral(phi) && valuation.isFixed(phi)

    if (member(conjectures, TNode(phi)) && valuation.isSatLiteral(phi) && valuation.isFixed(phi))
    {
      result.insert(phi);
      // out << "getProvedConjectures: fixed sat literal " << phi << " is a conjecture" << std::endl;
    }
    else if (valuation.isSatLiteral(phi) && valuation.isFixed(phi))
    {
      // out << "getProvedConjectures: fixed sat literal " << phi << " is not a conjecture" << std::endl;
    }
    else if (valuation.isSatLiteral(phi) && member(conjectures, TNode(phi)))
    {
      // out << "getProvedConjectures: sat literal " << phi << " is not fixed, but is a conjecture" << std::endl;
    }
    else if (member(conjectures, TNode(phi)))
    {
      // out << "getProvedConjectures: conjecture " << phi << " is not a sat literal" << std::endl;
    }
    else if (valuation.isSatLiteral(phi))
    {
      // out << "getProvedConjectures: sat literal " << phi << " is not a conjecture" << std::endl;
    }
    else
    {
      // out << "getProvedConjectures: " << phi << " is neither a sat literal nor a conjecture" << std::endl;
    }
  }

  return result;
}

void EnumerativeConjectureGenerator::check(CVC5_UNUSED Theory::Effort effort,
                                           QEffort qEffort)
{
  beginCallDebug();

  if (!d_initialFacts)
  {
    d_initialFacts = getInitialFacts(d_qstate.getValuation(), d_treg);
  }

  const Set<TNode> provedConjectures =
      getProvedConjectures(d_conjectures, d_qstate.getValuation(), d_treg);

  Assert(d_initialFacts);

  d_initialFacts->insert(provedConjectures.begin(), provedConjectures.end());

  debugPrintFacts(Trace("enumerative-conjecture-generator"), *d_initialFacts);

  if (qEffort == QEFFORT_STANDARD)
  {
    updateClock(d_clock, d_period);

    if (d_clock == 0)
    {
      checkHelper();      
    }
  }

  endCallDebug();
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
    const Map<TypeNode, std::uint8_t>& typeToNumber,
    const Node term,
    Map<Node, Index>& rootVariableToIndex)
{
  /* To implement this function we do the following:
   *
   * - collect the bound variables in `term` in a vector,
   * - sort the vector in increasing order of canonical variable index,
   * - go deeper in d_variableToIndex according to the sorted vector,
   * - when you're at the end of the vector add the term to d_terms.
   */
  Vector<Node> variables = getSortedVariables(termCanonize, typeToNumber, term);

  CIt<Vector<Node>> variableRef = variables.begin();

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
    jobs.emplace_back(new Job{std::vector<Node>{std::get<0>(*entryPtr)},
                              &std::get<1>(*entryPtr)});
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
      std::vector<Node> branchPath;
      branchPath.insert(branchPath.end(), path.begin(), path.end());
      branchPath.push_back(std::get<0>(*entryPtr));

      jobs.emplace_back(new Job{branchPath, &std::get<1>(*entryPtr)});
    }

    delete job;
  }
}

bool EnumerativeConjectureGenerator::variableLessThan(
    const expr::TermCanonize& termCanonize,
    const Map<TypeNode, std::uint8_t>& typeToNumber,
    TNode n0,
    TNode n1)
{
  const std::uint8_t t0 = typeToNumber.at(n0.getType());
  const std::uint8_t t1 = typeToNumber.at(n1.getType());
  const size_t i0 = termCanonize.getIndexForFreeVariable(n0);
  const size_t i1 = termCanonize.getIndexForFreeVariable(n1);

  return t0 < t1 || (t0 == t1 && i0 < i1);
}

std::vector<Node> EnumerativeConjectureGenerator::getSortedVariables(
    const expr::TermCanonize& termCanonize,
    const Map<TypeNode, std::uint8_t>& typeToNumber,
    TNode term)
{
  Set<Node> variables;

  expr::getSubtermsKind(Kind::BOUND_VARIABLE, term, variables);

  Vector<Node> result(variables.cbegin(), variables.cend());

  std::sort(result.begin(),
            result.end(),
            [&termCanonize, &typeToNumber](TNode n0, TNode n1) {
              return variableLessThan(termCanonize, typeToNumber, n0, n1);
            });

  return result;
}

std::vector<std::vector<Node>> EnumerativeConjectureGenerator::findCompatible(
    const size_t maximumSize,
    const size_t maximumDifference,
    const Map<Node, Index>& rootVariableToIndex,
    expr::TermCanonize& termCanonize,
    const Map<TypeNode, std::uint8_t>& typeToNumber,
    TNode canonical)
{
  TNode lhs = canonical[0];
  const TypeNode lhsType = lhs.getType();
  const bool lhsIsApplyCtor = lhs.getKind() == Kind::APPLY_CONSTRUCTOR;

  Vector<Vector<Node>> result;

  result.resize(maximumSize + 1);

  const Vector<Node> variables =
      getSortedVariables(termCanonize, typeToNumber, canonical);

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
        if (lhsType == (*jTerm)[0].getType()
            && (!lhsIsApplyCtor
                || (*jTerm)[0].getKind() != Kind::APPLY_CONSTRUCTOR))
        {
          result[computeSize(*jTerm)].push_back(*jTerm);
        }
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
    const bool preferActiveTerms,
    const std::int64_t substitutionLimit)
{
  Vector<Subs> substitutions;
  std::int64_t substitutionsSize = 0;
  Vector<Node> preferredClasses;

  for (eq::EqClassesIterator reprPtr = eq::EqClassesIterator(equalityEngine);
       !reprPtr.isFinished();
       ++reprPtr)
  {
    TNode repr = *reprPtr;

    const std::function<bool()> reprIsConst = [repr]() {
      return repr.isConst();
    };

    if (repr.getType() == canonical.getType()
        && implies(preferConstRepresentatives, reprIsConst))
    {
      preferredClasses.push_back(repr);
    }
  }

  for (CIt<Vector<Node>> reprPtr = preferredClasses.begin();
       reprPtr != preferredClasses.end();
       ++reprPtr)
  {
    TNode repr = *reprPtr;

    Vector<Decision*> decisionQueue;

    decisionQueue.emplace_back(new Decision(termDatabase,
                                            equalityEngine,
                                            canonical,
                                            repr,
                                            preferConstRepresentatives,
                                            preferActiveTerms));

    size_t virtualBegin = 0;

    Subs substitution;

    while (!decisionQueue.empty() && virtualBegin <= decisionQueue.size()
           && (!(virtualBegin < decisionQueue.size()
                 && decisionQueue[virtualBegin]->isFinished())
               || virtualBegin > 0)
           && (!(substitutionLimit != -1)
               || substitutionsSize <= substitutionLimit))
    {
      if (virtualBegin == decisionQueue.size())
      {
        // virtualBegin > 0 because decisionQueue.size() > 0

        substitutions.push_back(substitution);

        ++substitutionsSize;

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
}

void EnumerativeConjectureGenerator::debugPrintAssertions(
    std::ostream& out, const Vector<Node>& assertions)
{
  out << "Subsolver knows:" << std::endl;
  for (CIt<Vector<Node>> assertion = assertions.begin();
       assertion != assertions.end();
       ++assertion)
  {
    out << *assertion << std::endl;
  }
  out << "*****" << std::endl;
}

bool EnumerativeConjectureGenerator::isEntailed(
    Env& env,
    Options& defaultOpts,
    CVC5_UNUSED quantifiers::TermRegistry& termReg,
    const Vector<Node>& extra,
    const bool induct,
    const size_t timeout,
    const Set<TNode>& initialFacts,
    TNode conj)
{
  const bool instStrategyOn = TraceChannel.isOn("inst-strategy");
  const bool quantifiersSkOn = TraceChannel.isOn("quantifiers-sk");
  const bool instOn = TraceChannel.isOn("inst");

  if (instStrategyOn) TraceChannel.off("inst-strategy");
  if (quantifiersSkOn) TraceChannel.off("quantifiers-sk");
  if (instOn) TraceChannel.off("inst");

  Ptr<SolverEngine> subsolver;

  Options subsolverOpts;
  subsolverOpts.copyValues(defaultOpts);

  if (induct)
  {
    subsolverOpts.write_quantifiers().dtStcInduction = true;
    subsolverOpts.write_quantifiers().quantInduction = true;
  }

  smt::SetDefaults::disableChecking(subsolverOpts);

  SubsolverSetupInfo setupInfo(env, subsolverOpts);

  initializeSubsolver(
      env.getNodeManager(), subsolver, setupInfo, true, timeout);

  for (CIt<Set<TNode>> assertion = initialFacts.begin();
       assertion != initialFacts.end();
       ++assertion)
  {
    subsolver->assertFormula(*assertion);
  }

  /*
  We comment out the following block because we do not want to rely on
  quantified formulas that are at decision level 1 or higher when checking
  whether a formula is entailed.
  */

  // quantifiers::FirstOrderModel* model = termReg.getModel();
  //
  // for (size_t i = 0; i < model->getNumAssertedQuantifiers(); i++)
  // {
  //   TNode phi = model->getAssertedQuantifier(i);
  //   subsolver->assertFormula(phi);
  // }

  for (CIt<Vector<Node>> phi = extra.begin(); phi != extra.end(); ++phi)
  {
    subsolver->assertFormula(*phi);
  }

  subsolver->assertFormula(conj.negate());

  const Vector<Node> subsolverAssertions = subsolver->getAssertions();

  const Result result = subsolver->checkSat();

  if (instStrategyOn) TraceChannel.on("inst-strategy");
  if (quantifiersSkOn) TraceChannel.on("quantifiers-sk");
  if (instOn) TraceChannel.on("inst");

  return result.getStatus() == Result::UNSAT;
}

bool EnumerativeConjectureGenerator::filterConjecture(
    Env& env,
    Options& subsolverOpts,
    quantifiers::TermRegistry& termReg,
    Set<Node>& indEnt,
    Set<Node>& dedEnt,
    Vector<Node>& indEntBuf,
    Optional<std::int64_t>& fuel,
    const size_t timeout,
    const Set<TNode>& initialFacts,
    TNode conj,
    const Set<TNode>& conjectures,
    const TNode trueNode,
    const quantifiers::QuantifiersState& quantifiersState,
    const bool split)
{
  FilterResult result = NONE;

  if (quantifiersState.areEqual(conj, trueNode))
  {
    result = TRIVIAL;
  }
  else if (member(indEnt, Node(conj)) || member(dedEnt, Node(conj))
           || member(conjectures, conj))
  {
    result = CACHED;
  }
  // Entailment checks are always helpful.  However they aren't necessary when split is true and we're eventually going to assert a splitting lemma for the conjecture.  Let's avoid subsolver-based entailment checks when split is true.
  else if (!split && isEntailed(env,
                      subsolverOpts,
                      termReg,
                      indEntBuf,
                      false,
                      timeout,
                      initialFacts,
                      conj))
  {
    dedEnt.insert(conj);

    result = DEDUCTIVE;
  }
  else if (!split && isEntailed(env,
                      subsolverOpts,
                      termReg,
                      indEntBuf,
                      true,
                      timeout,
                      initialFacts,
                      conj))
  {
    indEnt.insert(conj);

    indEntBuf.push_back(conj);

    if (fuel)
    {
      fuel.emplace(*fuel - 1);
    }

    result = INDUCTIVE;
  }

  return (split || result == INDUCTIVE);
}

void EnumerativeConjectureGenerator::assertConjecture(
    quantifiers::QuantifiersInferenceManager& quantInfMgr, TNode conj, const bool split, const Vector<Node>& indEntBuf)
{
  if (split)
  {
    Node lem = NodeManager::mkNode(Kind::OR, conj.negate(), conj);
    Trace("enumerative-conjecture-generator") << "* asserting " << lem << std::endl;
    quantInfMgr.addPendingLemma(lem, InferenceId::QUANTIFIERS_ENUMERATIVE_CONJECTURE_GENERATOR);
    quantInfMgr.addPendingPhaseRequirement(conj, false);
  }
  else
  {
    Assert(member(indEntBuf, Node(conj)));
    quantInfMgr.addPendingLemma(conj, InferenceId::QUANTIFIERS_ENUMERATIVE_CONJECTURE_GENERATOR);
  }
}

Node EnumerativeConjectureGenerator::candidateToConjecture(
    NodeManager* nodeMgr, const Candidate& cand, theory::Rewriter* rewriter)
{
  Node lhs = cand.d_left;
  Set<Node> vars;
  expr::getFreeVariables(lhs, vars);
  Node bvs = nodeMgr->mkNode(Kind::BOUND_VAR_LIST,
                             Vector<Node>(vars.begin(), vars.end()));
  Node rhs = cand.d_right;
  Assert(lhs.getType() == rhs.getType());
  Node eq = lhs.eqNode(rhs);
  Node result = nodeMgr->mkNode(Kind::FORALL, bvs, eq);
  if (rewriter != nullptr)
  {
    Node rewritten = rewriter->rewrite(result);
    result = rewritten;
  }
  return result;
}

void EnumerativeConjectureGenerator::filterCandidates(
    Env& env,
    Options& subsolverOpts,
    quantifiers::QuantifiersInferenceManager& quantInfMgr,
    quantifiers::TermRegistry& termReg,
    NodeManager* nodeMgr,
    const std::int64_t initialFuel,
    Set<Node>& indEnt,
    Set<Node>& dedEnt,
    const size_t timeout,
    const Set<TNode>& initialFacts,
    Vector<PriorityQueue<Candidate>>& candIdx,
    Set<TNode>& conjectures,
    const quantifiers::QuantifiersState& quantifiersState,
    const bool split)
{
  Optional<std::int64_t> fuel(initialFuel);

  if (initialFuel == -1)
  {
    fuel.reset();
  }

  Vector<Node> indEntBuf;

  for (It<Vector<PriorityQueue<Candidate>>> candsPtr = candIdx.begin();
       candsPtr != candIdx.end();
       ++candsPtr)
  {
    PriorityQueue<Candidate>& cands = *candsPtr;

    while (!cands.empty())
    {
      const Candidate cand = cands.top();

      cands.pop();

      Node conj = candidateToConjecture(nodeMgr, cand, env.getRewriter());

      if (filterConjecture(env,
                           subsolverOpts,
                           termReg,
                           indEnt,
                           dedEnt,
                           indEntBuf,
                           fuel,
                           timeout,
                           initialFacts,
                           conj,
                           conjectures,
                           nodeMgr->mkConst(true),
                           quantifiersState,
                           split))
      {
        conjectures.insert(conj);

        assertConjecture(quantInfMgr, conj, split, indEntBuf);

        if (fuel && *fuel < 1)
        {
          return;
        }
      }
    }
  }
}

void EnumerativeConjectureGenerator::debugPrintFilterConjecture(
    std::ostream& out, TNode conj, FilterResult result)
{
  out << "Conjecture " << conj << " is " << result << std::endl;
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
