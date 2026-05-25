#include "theory/quantifiers/enumerative_conjecture_generator.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "expr/sygus_grammar.h"
#include "theory/datatypes/sygus_datatype_utils.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
static std::ostream& operator<<(std::ostream& out, std::vector<TypeNode>& vec)
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
}

EnumerativeConjectureGenerator::~EnumerativeConjectureGenerator() {}

bool EnumerativeConjectureGenerator::needsCheck(Theory::Effort e)
{
  return d_qstate.getInstWhenNeedsCheck(e);
}

void EnumerativeConjectureGenerator::reset_round(Theory::Effort) {}

void EnumerativeConjectureGenerator::check(Theory::Effort, QEffort)
{
  beginCallDebug();

  std::ostream& ecg = Trace("enumerative-conjecture-generator");

  // We clear `d_rlvFuncSyms`.

  d_rlvFuncSyms.clear();
  d_rlvTypes.clear();

  // We populate `d_rlvFuncSyms`.

  TermDb* termDb = getTermDatabase();

  for (size_t i = 0; i < termDb->getNumOperators(); ++i)
  {
    Node op = termDb->getOperator(i);

    // We only want to move ahead when `op` is an uninterpreted function symbol
    // or a constructor symbol.  As it stands `op` might be an application of a
    // selector symbol or a tester symbol.  We **do not** want to proceed when
    // `op` is an application of a selector symbol or a tester symbol.  Let's
    // use the next block of code to set the value of `skip_op`.

    bool skipOp = false;

    if (op.hasOperator())
    {
      skipOp = true;
    }
    else if (termDb->getNumGroundTerms(op) == 0)
    {
      skipOp = true;
    }

    // If `skipOp` is true we print that we're ignoring `op`.  Otherwise we
    // print that we're considering `op`.

    if (skipOp)
    {
    }
    else
    {
      TNode groundTerm = termDb->getGroundTerm(op, 0);

      d_symbolToKind[op] = groundTerm.getKind();

      d_rlvFuncSyms.push_back(op);
    }
  }

  // We populate `d_rlvTypes`.

  for (std::vector<TNode>::iterator funcRef = d_rlvFuncSyms.begin();
       funcRef != d_rlvFuncSyms.end();
       ++funcRef)
  {
    TNode func = *funcRef;
    TypeNode fullTyp = func.getType();
    for (TypeNode::iterator typRef = fullTyp.begin(); typRef != fullTyp.end();
         ++typRef)
    {
      TypeNode typ = *typRef;
      if (!EnumerativeConjectureGenerator::member(d_rlvTypes, typ))
      {
        d_rlvTypes.push_back(typ);
      }
    }
  }

  // We display `d_rlvTypes`.

  // ecg << "Relevant types are " << d_rlvTypes << std::endl;

  // We create the grammar.

  SkolemManager* skolemManager = d_nodeManager->getSkolemManager();

  typedef std::vector<TypeNode>::iterator TypeRef;

  for (TypeRef typeRef = d_rlvTypes.begin(); typeRef != d_rlvTypes.end();
       ++typeRef)
  {
    const TypeNode domainType = *typeRef;

    if (!hasKey(d_typeToIn, domainType))
    {
      const TypeNode inType = d_nodeManager->mkFunctionType(domainType, d_rootType);
      const Node inFunc = skolemManager->mkDummySkolem("in", inType);
      d_typeToIn[domainType] = inFunc;
    }

    if (!hasKey(d_typeToNonTerminal, domainType))
    {
      const Node nonTerminal = NodeManager::mkBoundVar("nt", domainType);
      d_typeToNonTerminal[domainType] = nonTerminal;
    }

    if (!hasKey(d_typeToVariables, domainType))
    {
      std::vector<Node> variables;

      for (size_t i = 0; i < d_maximumSize - 1; ++i)
      {
        variables.push_back(d_termCanonize.getCanonicalFreeVar(domainType, i));
      }

      d_typeToVariables[domainType] = variables;
    }
  }

  std::vector<Node> nonTerminals;

  nonTerminals.push_back(d_rootNonTerminal);

  for (TypeRef typeRef = d_rlvTypes.begin(); typeRef != d_rlvTypes.end();
       ++typeRef)
  {
    nonTerminals.push_back(d_typeToNonTerminal[*typeRef]);
  }

  SygusGrammar grammar = SygusGrammar(std::vector<Node>{}, nonTerminals);

  /* We add the rules to map terms of the relevant types into the type of the
     root non-terminal. */

  for (TypeRef typeRef = d_rlvTypes.begin(); typeRef != d_rlvTypes.end();
       ++typeRef)
  {
    const TypeNode relevantType = *typeRef;
    const Node nonTerminal = d_typeToNonTerminal[relevantType];
    const Node inFunction = d_typeToIn[relevantType];
    const Node rule =
        d_nodeManager->mkNode(Kind::APPLY_UF, inFunction, nonTerminal);

    // ecg << "We're going to add the rule " << rule << std::endl;

    grammar.addRule(d_rootNonTerminal, rule);
  }

  /* We add rules corresponding to the relevant function symbols. */

  typedef std::vector<TNode>::iterator TNodeRef;

  for (TNodeRef tNodeRef = d_rlvFuncSyms.begin();
       tNodeRef != d_rlvFuncSyms.end();
       ++tNodeRef)
  {
    const TNode rlvFunc = *tNodeRef;

    const TypeNode rlvFuncType = rlvFunc.getType();

    std::vector<Node> application = {rlvFunc};

    const TypeNode::iterator rangeRef = rlvFuncType.end() - 1;

    for (TypeNode::iterator typeRef = rlvFuncType.begin(); typeRef != rangeRef;
         ++typeRef)
    {
      application.push_back(d_typeToNonTerminal[*typeRef]);
    }

    const Kind kind = d_symbolToKind[rlvFunc];

    const Node rule = d_nodeManager->mkNode(kind, application);

    // ecg << "We're going to add the rule " << rule << std::endl;

    TNode nonTerminal = d_typeToNonTerminal[*rangeRef];

    grammar.addRule(nonTerminal, rule);
  }

  /* We add rules for the free variables. */

  for (std::vector<TypeNode>::iterator typeRef = d_rlvTypes.begin();
       typeRef != d_rlvTypes.end();
       ++typeRef)
  {
    const TypeNode type_ = *typeRef;

    TNode nonTerminal = d_typeToNonTerminal[type_];

    const std::vector<Node>& variables = d_typeToVariables[type_];

    for (std::vector<Node>::const_iterator variableRef = variables.begin();
         variableRef != variables.end();
         ++variableRef)
    {
      grammar.addRule(nonTerminal, *variableRef);
    }
  }

  /* We resolve the grammar. */

  const TypeNode grammarType = grammar.resolve();

  // ecg << "Grammar is ";
  // if (!grammar.isResolved())
  // {
  //   ecg << "not ";
  // }
  // ecg << "resolved" << std::endl;

  /* We enumerate terms from the grammar. */

  SygusTermEnumerator sygusTermEnumerator = SygusTermEnumerator(
      d_env,
      grammarType,
      new EnumerativeConjectureGeneratorCallback(this, d_maximumSize - 1),
      false,
      0);

  bool keepGoing = true;

  std::vector<std::unordered_set<Node>> sizeToCanonicals;

  sizeToCanonicals.resize(d_maximumSize + 1);

  while (keepGoing)
  {
    const Node currentTerm = sygusTermEnumerator.getCurrent();

    if (!currentTerm.isNull())
    {
      if (underestimateSize(currentTerm) > d_maximumSize)
      {
        keepGoing = false;
      }
      else
      {
        std::unordered_set<Node> boundVariableSet;

        expr::getSubtermsKind(
            Kind::BOUND_VARIABLE, currentTerm, boundVariableSet);

        std::unordered_set<Node> ufApplicationSet;

        expr::getSubtermsKind(
            Kind::APPLY_UF, currentTerm[0], ufApplicationSet, false);

        if (!boundVariableSet.empty() && !ufApplicationSet.empty())
        {
          addTerm(currentTerm, boundVariableSet);

          Node canonical =
              d_termCanonize.getCanonicalTerm(currentTerm, false, false);

          size_t size = computeSize(canonical);

          std::unordered_set<Node>& canonicals = sizeToCanonicals[size];

          canonicals.insert(canonical);
        }
      }
    }

    keepGoing = keepGoing && sygusTermEnumerator.increment();
  }

  // debugPrintIndex(ecg);

  // ecg << "Canonical terms:" << std::endl;

  // for (size_t currentSize = 0; currentSize <= d_maximumSize; ++currentSize)
  // {
  //   ecg << "Size " << currentSize << std::endl;

  //   const std::vector<Node>& canonicals = sizeToCanonicals[currentSize];

  //   for (std::vector<Node>::const_iterator termRef = canonicals.begin();
  //        termRef != canonicals.end();
  //        ++termRef)
  //   {
  //     ecg << "Term " << *termRef << std::endl;
  //   }
  // }

  std::unordered_set<Node>& canonicals3 = sizeToCanonicals[3];

  size_t fuel = 10;

  for (std::unordered_set<Node>::const_iterator termRef = canonicals3.begin();
       termRef != canonicals3.end();
       ++termRef)
  {
    if (fuel < 1)
    {
      break;
    }

    std::vector<std::vector<Node>> sizeToCompatible = findCompatible(*termRef);

    ecg << "RHS terms for LHS " << *termRef << std::endl;

    for (size_t rhsSize = 0; rhsSize <= d_maximumSize; ++rhsSize)
    {
      std::vector<Node>& compatible = sizeToCompatible[rhsSize];

      if (!compatible.empty())
      {
        ecg << "Terms with size " << rhsSize << std::endl;

        for (std::vector<Node>::const_iterator rhsRef = compatible.begin();
             rhsRef != compatible.end();
             ++rhsRef)
        {
          ecg << "Term " << *rhsRef << std::endl;
        }
      }
    }

    --fuel;
  }

  std::unordered_map<Node, std::vector<Node>> canonicalToRhs;

  endCallDebug();
}

size_t EnumerativeConjectureGenerator::underestimateSize(TNode n)
{
  struct Job
  {
    TNode d_out;
  };

  std::vector<Job*> jobs = {new Job{n}};

  size_t result = 1;

  while (!jobs.empty())
  {
    const Job* currentJob = jobs.back();

    jobs.pop_back();

    const TNode currentN = currentJob->d_out;

    const Kind nKind = currentN.getKind();

    if (nKind == Kind::APPLY_CONSTRUCTOR || nKind == Kind::APPLY_UF)
    {
      TNode::iterator childRef = currentN.begin();

      const TNode::iterator childRefMax = currentN.end();

      if (childRef != childRefMax)
      {
        ++result;

        for (; childRef != childRefMax; ++childRef)
        {
          jobs.push_back(new Job{*childRef});
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
    TNode d_out;
  };

  std::vector<Job*> jobs = {new Job{n}};

  size_t result = 0;

  std::unordered_set<TNode> seen;

  while (!jobs.empty())
  {
    const Job* currentJob = jobs.back();

    jobs.pop_back();

    const TNode currentN = currentJob->d_out;

    const Kind nKind = currentN.getKind();

    if (nKind == Kind::BOUND_VARIABLE && member(seen, currentN))
    {
      ++result;
    }
    else if (nKind == Kind::BOUND_VARIABLE)
    {
      seen.insert(currentN);
    }
    else if (nKind == Kind::APPLY_CONSTRUCTOR || nKind == Kind::APPLY_UF)
    {
      ++result;

      for (TNode::iterator childRef = currentN.begin();
           childRef != currentN.end();
           ++childRef)
      {
        jobs.push_back(new Job{*childRef});
      }
    }

    delete currentJob;
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
  const Node n = datatypes::utils::sygusToBuiltin(sygusN);

  if (n.getType() != d_enumerativeConjectureGenerator->d_rootType
      && d_enumerativeConjectureGenerator->computeSize(n) > d_maximumSize)
  {
    // Trace("enumerative-conjecture-generator") << "Reject " << n << std::endl;

    return false;
  }

  return true;
}

void EnumerativeConjectureGenerator::addTerm(
    Node term, std::unordered_set<Node>& boundVariableSet)
{
  /* To implement this function we do the following:
   *
   * - collect the bound variables in `term` in a vector,
   * - sort the vector in increasing order of canonical variable index,
   * - go deeper in d_variableToIndex according to the sorted vector,
   * - when you're at the end of the vector add the term to d_terms.
   */
  std::vector<Node> boundVariables;

  boundVariables.insert(
      boundVariables.end(), boundVariableSet.begin(), boundVariableSet.end());

  std::sort(
      boundVariables.begin(), boundVariables.end(), [this](Node n0, Node n1) {
        return this->d_termCanonize.getIndexForFreeVariable(n0)
               < this->d_termCanonize.getIndexForFreeVariable(n1);
      });

  std::vector<Node>::const_iterator variableRef = boundVariables.begin();

  Index* currentIndex = &d_variableToIndex[*variableRef];

  ++variableRef;

  for (; variableRef != boundVariables.end(); ++variableRef)
  {
    currentIndex = &currentIndex->d_variableToIndex[*variableRef];
  }

  currentIndex->d_terms.push_back(term);
}

void EnumerativeConjectureGenerator::debugPrintIndex(std::ostream& out)
{
  struct Job
  {
    Index* d_index;
    std::vector<Node> d_path;
  };

  std::vector<Job*> jobs;

  for (std::map<Node, Index>::iterator entryRef = d_variableToIndex.begin();
       entryRef != d_variableToIndex.end();
       ++entryRef)
  {
    jobs.push_back(new Job{&std::get<1>(*entryRef),
                           std::vector<Node>{std::get<0>(*entryRef)}});
  }

  while (!jobs.empty())
  {
    Job* job = jobs.back();

    jobs.pop_back();

    Index* index = job->d_index;

    std::vector<Node>& terms = index->d_terms;

    std::vector<Node>& path = job->d_path;

    out << "Path " << path << std::endl;

    for (std::vector<Node>::iterator termRef = terms.begin();
         termRef != terms.end();
         ++termRef)
    {
      out << "Term " << *termRef << std::endl;
    }

    for (std::map<Node, Index>::iterator entryRef =
             index->d_variableToIndex.begin();
         entryRef != index->d_variableToIndex.end();
         ++entryRef)
    {
      std::vector<Node> newPath;

      newPath.insert(newPath.end(), path.begin(), path.end());

      newPath.push_back(std::get<0>(*entryRef));

      jobs.push_back(new Job{&std::get<1>(*entryRef), newPath});
    }

    delete job;
  }
}

std::vector<std::vector<Node>> EnumerativeConjectureGenerator::findCompatible(
    TNode lhs)
{
  std::ostream& ecg = Trace("enumerative-conjecture-generator");

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
  };

  std::vector<Job*> jobs;

  for (size_t position = 0; position < variableCount; ++position)
  {
    TNode variable = variables[position];

    if (hasKey(d_variableToIndex, variable))
    {
      jobs.push_back(new Job{position + 1, &d_variableToIndex[variable]});
    }
  }

  while (!jobs.empty())
  {
    Job* job = jobs.back();

    jobs.pop_back();

    size_t jobPosition = job->d_position;

    Index* jobIndex = job->d_index;

    std::vector<Node>& jobTerms = jobIndex->d_terms;

    std::map<Node, Index>& jobVariableToIndex = jobIndex->d_variableToIndex;

    for (std::vector<Node>::const_iterator termRef = jobTerms.begin();
         termRef != jobTerms.end();
         ++termRef)
    {
      Node term = *termRef;

      const size_t termSize = computeSize(term);

      sizeToCompatible[termSize].push_back(term);
    }

    for (size_t position = jobPosition; position < variableCount; ++position)
    {
      TNode variable = variables[position];

      if (hasKey(jobVariableToIndex, variable))
      {
        jobs.push_back(new Job{position + 1, &jobVariableToIndex[variable]});
      }
    }

    delete job;
  }

  return sizeToCompatible;
}
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
