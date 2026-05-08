#include "theory/quantifiers/enumerative_conjecture_generator.h"

#include "expr/skolem_manager.h"
#include "expr/sygus_grammar.h"

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
  d_rootType = d_nodeManager->mkSort();
  d_rootNonTerminal = NodeManager::mkBoundVar(d_rootType);
}

EnumerativeConjectureGenerator::~EnumerativeConjectureGenerator() {}

bool EnumerativeConjectureGenerator::needsCheck(Theory::Effort e)
{
  return d_qstate.getInstWhenNeedsCheck(e);
}

void EnumerativeConjectureGenerator::reset_round(Theory::Effort e) {}

void EnumerativeConjectureGenerator::check(Theory::Effort e, QEffort quantE)
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
      if (EnumerativeConjectureGenerator::member(d_rlvTypes, typ))
      {
      }
      else
      {
        d_rlvTypes.push_back(typ);
      }
    }
  }

  // We display `d_rlvTypes`.

  ecg << "Relevant types are " << d_rlvTypes << std::endl;

  // We create the grammar.

  SkolemManager* skolemManager = d_nodeManager->getSkolemManager();

  typedef std::vector<TypeNode>::iterator TypeRef;

  for (TypeRef typeRef = d_rlvTypes.begin(); typeRef != d_rlvTypes.end();
       ++typeRef)
  {
    const TypeNode domainType = *typeRef;

    if (hasKey(d_typeToIn, domainType))
    {
    }
    else
    {
      const TypeNode inType = d_nodeManager->mkFunctionType(inType, d_rootType);
      const Node inFunc = skolemManager->mkDummySkolem("in", inType);
      d_typeToIn[domainType] = inFunc;
    }

    if (hasKey(d_typeToNonTerminal, domainType))
    {
    }
    else
    {
      const Node nonTerminal = NodeManager::mkBoundVar(domainType);
      d_typeToNonTerminal[domainType] = nonTerminal;
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

  for (TypeRef typeRef = d_rlvTypes.begin(); typeRef != d_rlvTypes.end();
       ++typeRef)
  {
    const TypeNode relevantType = *typeRef;
    const Node nonTerminal = d_typeToNonTerminal[relevantType];
    const Node inFunction = d_typeToIn[relevantType];
    const Node rule = d_nodeManager->mkNode(Kind::APPLY_UF, inFunction, nonTerminal);
    
    ecg << "We're going to add the rule " << rule << std::endl;

    grammar.addRule(d_rootNonTerminal, rule);
  }

  typedef std::vector<TNode>::iterator TNodeRef;

  for (TNodeRef tNodeRef = d_rlvFuncSyms.begin(); tNodeRef != d_rlvFuncSyms.end(); ++tNodeRef)
  {
    const TNode rlvFunc = *tNodeRef;

    const TypeNode rlvFuncType = rlvFunc.getType();

    std::vector<Node> application = { rlvFunc };

    const TypeNode::iterator rangeRef = rlvFuncType.end() - 1;

    for (TypeNode::iterator typeRef = rlvFuncType.begin(); typeRef != rangeRef; ++typeRef)
    {
      application.push_back(d_typeToNonTerminal[*typeRef]);
    }

    const Kind kind = d_symbolToKind[rlvFunc];

    const Node rule = d_nodeManager->mkNode(kind, application);

    ecg << "We're going to add the rule " << rule << std::endl;

    TNode nonTerminal = d_typeToNonTerminal[*rangeRef];

    grammar.addRule(nonTerminal, rule);
  }

  endCallDebug();
}

std::string EnumerativeConjectureGenerator::identify() const
{
  return "enumerative-conjecture-generator";
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
