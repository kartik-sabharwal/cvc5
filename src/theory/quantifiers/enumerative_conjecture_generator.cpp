#include "theory/quantifiers/enumerative_conjecture_generator.h"

#include <sstream>
#include <unordered_map>
#include <unordered_set>

#include "cvc5_public.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "expr/subs.h"
#include "expr/sygus_grammar.h"
#include "preprocessing/passes/synth_rew_rules.h"
#include "theory/datatypes/sygus_datatype_utils.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
CVC5_UNUSED static std::ostream& operator<<(std::ostream& out,
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
    Node ithOperator = termDatabase->getOperator(i);

    const Kind kind = ithOperator.getKind();

    bool relevant = true;

    if (kind == Kind::APPLY_TESTER || kind == Kind::APPLY_SELECTOR
        || termDatabase->getNumGroundTerms(ithOperator) == 0)
    {
      relevant = false;
    }

    if (relevant)
    {
      result.push_back(ithOperator);
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

  CVC5_UNUSED std::vector<std::unordered_set<Node>>& sizeToCanonicals =
      std::get<0>(enumerationData);

  CVC5_UNUSED std::unordered_map<Node, Index>& variableToIndex =
      std::get<1>(enumerationData);

  debugPrintSizeToCanonicals(traceStream, d_maximumSize, sizeToCanonicals);

  debugPrintIndex(traceStream, variableToIndex);

  // traceStream << d_qstate.getEqualityEngine()->debugPrintEqc();

  // TypeNode natType = findTypeByName("Nat");
  // Assert(!natType.isNull());
  // Node timesSymbol = findFunctionSymbolByName("times");
  // Assert(!timesSymbol.isNull());
  // Node n0Symbol = d_termCanonize.getCanonicalFreeVar(natType, 0);
  // Node n1Symbol = d_termCanonize.getCanonicalFreeVar(natType, 1);
  // Node pattern = nodeManager()->mkNode(
  //     Kind::APPLY_UF, std::vector<Node>{timesSymbol, n0Symbol, n1Symbol});
  // traceStream << "d_preferConstRepresentatives := "
  //             << d_preferConstRepresentatives
  //             << ", d_preferActiveTerms := " << d_preferActiveTerms <<
  //             std::endl
  //             << "Substitutions for " << pattern << " are:" << std::endl;
  // std::vector<Subs> substitutions = findSubstitutions(
  //     pattern, d_preferConstRepresentatives, d_preferActiveTerms);
  // for (std::vector<Subs>::const_iterator substitutionRef =
  //          substitutions.begin();
  //      substitutionRef != substitutions.end();
  //      ++substitutionRef)
  // {
  //   traceStream << *substitutionRef << std::endl;
  // }

  // std::unordered_map<Node, std::vector<std::vector<Node>>>
  //     canonicalToSizeToCandidates;

  // Count substitutions for each canonical term.
  // for (size_t canonicalSize = 1; canonicalSize <= d_maximumSize;
  //      ++canonicalSize)
  // {
  //   std::unordered_set<Node>& canonicals =
  //   sizeToCanonicals[canonicalSize];

  //   for (std::unordered_set<Node>::const_iterator canonicalRef =
  //            canonicals.begin();
  //        canonicalRef != canonicals.end();
  //        ++canonicalRef)
  //   {
  //     TNode canonical = *canonicalRef;

  //     TNode pattern = canonical[0];

  //     std::vector<Subs> substitutions = findSubstitutions(
  //         pattern, d_preferConstRepresentatives, d_preferActiveTerms);

  //     ecg << "There are " << substitutions.size()
  //         << " substitutions for the canonical term " << pattern
  //         << std::endl;
  //   }
  // }
  //

  endCallDebug();
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

EnumerativeConjectureGeneratorCallback::EnumerativeConjectureGeneratorCallback(
    EnumerativeConjectureGenerator* enumerativeConjectureGenerator,
    size_t maximumSize)
    : d_enumerativeConjectureGenerator(enumerativeConjectureGenerator),
      d_maximumSize(maximumSize) {};

bool EnumerativeConjectureGeneratorCallback::addTerm(const Node& sygusN,
                                                     std::unordered_set<Node>&)
{
  bool result = true;

  const Node n = datatypes::utils::sygusToBuiltin(sygusN);

  if (n.getType() != d_enumerativeConjectureGenerator->d_rootType
      && d_enumerativeConjectureGenerator->computeSize(n) > d_maximumSize)
  {
    result = false;
  }

  return result;
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
#define entry *entryPtr
    jobs.emplace_back(
        new Job{std::vector<Node>{std::get<0>(entry)}, &std::get<1>(entry)});
#undef entry
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
#define entry *entryPtr
      std::vector<Node> branchPath;
      branchPath.insert(branchPath.end(), path.begin(), path.end());
      branchPath.push_back(std::get<0>(entry));

      jobs.emplace_back(new Job{branchPath, &std::get<1>(entry)});
#undef entry
    }

    delete job;
  }
}

std::vector<std::vector<Node>> EnumerativeConjectureGenerator::findCompatible(
    TNode lhs)
{
  // std::ostream& ecg = Trace("enumerative-conjecture-generator");

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

std::vector<Subs> EnumerativeConjectureGenerator::findSubstitutions(
    TNode canonical,
    const bool preferConstRepresentatives,
    const bool preferActiveTerms)
{
  std::vector<Subs> substitutions;

  std::vector<Node> preferredRepresentatives;

  TermDb* termDatabase = getTermDatabase();

  eq::EqualityEngine* equalityEngine = d_qstate.getEqualityEngine();

  for (eq::EqClassesIterator representativeRef =
           eq::EqClassesIterator(equalityEngine);
       !representativeRef.isFinished();
       ++representativeRef)
  {
    Node representative = *representativeRef;

    if (representative.getType() == canonical.getType())
    {
      // preferConstRepresentatives ==> representative.isConst()
      if (!preferConstRepresentatives || representative.isConst())
      {
        preferredRepresentatives.push_back(representative);
      }
    }
  }

  for (std::vector<Node>::iterator representativeRef =
           preferredRepresentatives.begin();
       representativeRef != preferredRepresentatives.end();
       ++representativeRef)
  {
    Node representative = *representativeRef;

    Subs substitution;

    Trail decisionQueue;

    decisionQueue.emplace_back(new Decision(termDatabase,
                                            equalityEngine,
                                            canonical,
                                            representative,
                                            preferConstRepresentatives,
                                            preferActiveTerms));

    size_t decisionQueueFront = 0;

    bool goOn = true;

    while (goOn)
    {
      size_t decisionQueueBack = decisionQueue.size() - 1;

      const bool decisionQueueEmpty = decisionQueueFront > decisionQueueBack;

      if (decisionQueueEmpty)
      {
        substitutions.push_back(substitution);

        if (decisionQueueFront > 0)
        {
          decisionQueueFront = decisionQueueBack;

          decisionQueue[decisionQueueFront]->pop(substitution);
        }
        else
        {
          goOn = false;
        }
      }
      else
      {
        Decision* decision = decisionQueue[decisionQueueFront];

        if (decision->isFinished())
        {
          if (decisionQueueFront > 0)
          {
            for (size_t i = 0; i < decisionQueue.size() - decisionQueueFront;
                 ++i)
            {
              Decision* decisionToDelete = decisionQueue.back();

              decisionQueue.pop_back();

              delete decisionToDelete;
            }

            --decisionQueueFront;

            decisionQueue[decisionQueueFront]->pop(substitution);
          }
          else
          {
            goOn = false;
          }
        }
        else if (decision->push(
                     termDatabase, equalityEngine, substitution, decisionQueue))
        {
          ++decisionQueueFront;
        }
        else
        {
          decision->pop(substitution);
        }
      }
    }
  }

  return substitutions;
}

TypeNode EnumerativeConjectureGenerator::findTypeByName(const std::string& name)
{
  TypeNode result = TypeNode::null();

  std::vector<TypeNode>::const_iterator typeRef = std::find_if(
      d_relevantTypes.begin(),
      d_relevantTypes.end(),
      [name](const TypeNode& type) {
        const std::string typeName = (std::stringstream() << type).str();
        const int result = typeName.compare(name);
        return result == 0;
      });

  if (typeRef != d_relevantTypes.end())
  {
    result = *typeRef;
  }

  return result;
}

Node EnumerativeConjectureGenerator::findFunctionSymbolByName(
    const std::string& name)
{
  Node result = Node::null();

  std::vector<Node>::const_iterator functionSymbolRef =
      std::find_if(d_relevantFunctionSymbols.begin(),
                   d_relevantFunctionSymbols.end(),
                   [name](TNode functionSymbol) {
                     return functionSymbol.getName() == name;
                   });

  if (functionSymbolRef != d_relevantFunctionSymbols.end())
  {
    result = *functionSymbolRef;
  }

  return result;
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

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
