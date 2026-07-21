#include "theory/quantifiers/contextual_enumerator.h"

#include "expr/skolem_manager.h"
#include "expr/sygus_term_enumerator.h"
#include "theory/quantifiers/ematching/trigger_term_info.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/quantifiers/sygus_sampler.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

ContextualEnumerator::ContextualEnumerator(Env& env,
                                           QuantifiersState& qs,
                                           QuantifiersInferenceManager& qim,
                                           QuantifiersRegistry& qr,
                                           TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr)
{
}

ContextualEnumerator::~ContextualEnumerator() {}

bool ContextualEnumerator::needsCheck(Theory::Effort e)
{
  return d_qstate.getInstWhenNeedsCheck(e);
}

void ContextualEnumerator::reset_round(CVC5_UNUSED Theory::Effort e) {}

void ContextualEnumerator::check(CVC5_UNUSED Theory::Effort e, QEffort quant_e)
{
  beginCallDebug();

  if (quant_e == QEFFORT_STANDARD)
  {
    const std::vector<TNode> relevantFunctionSymbols =
        getRelevantFunctionSymbols(getTermDatabase());

    if (TraceIsOn("contextual-enumerator"))
    {  // Begin tracing code
      Trace("contextual-enumerator")
          << "Relevant function symbols are:" << std::endl;
      std::for_each(relevantFunctionSymbols.cbegin(),
                    relevantFunctionSymbols.cend(),
                    [](const TNode f) {
                      Trace("contextual-enumerator")
                          << "* " << f << " : " << f.getKind() << std::endl;
                    });
    }  // End tracing code

    NodeManager* nodeMgr = nodeManager();

    for (auto fIt = relevantFunctionSymbols.cbegin();
         fIt != relevantFunctionSymbols.cend();
         ++fIt)
    {
      const TNode f = *fIt;

      if (f.getKind() == Kind::VARIABLE
          && d_enumerated.find(f) == d_enumerated.end())
      {
        const TNode predicate = getPredicateForType(f.getType().getRangeType());

        const std::vector<Node> terms = enumerateTermsWithSygus(f);

        if (TraceIsOn("contextual-enumerator"))
        {  // Begin tracing code
          Trace("contextual-enumerator")
              << "Terms generated for operator " << f << " are:" << std::endl;
          std::for_each(terms.cbegin(), terms.cend(), [](const TNode term) {
            Trace("contextual-enumerator") << "* " << term << std::endl;
          });
        }  // End tracing code

        for (auto termIt = terms.cbegin(); termIt != terms.cend(); ++termIt)
        {
          const Node term = *termIt;

          const Node lemma = nodeMgr->mkNode(Kind::APPLY_UF, predicate, term);

          d_qim.addPendingLemma(lemma, InferenceId::QUANTIFIERS_CTX_ENUM);
        }

        d_enumerated.insert(f);
      }
    }
  }

  endCallDebug();
}

std::string ContextualEnumerator::identify() const
{
  return "contextual-enumerator";
}

std::vector<TNode> ContextualEnumerator::getRelevantFunctionSymbols(TermDb* tdb)
{
  std::unordered_set<TNode> result;

  for (size_t i = 0; i < tdb->getNumOperators(); ++i)
  {
    const TNode f = tdb->getOperator(i);

    const context::CDList<Node>& fList = tdb->getOrMkDbListForOp(f)->d_list;

    if (!fList.empty())
    {
      const TNode t = fList[0];

      if (isSymbolRelevant(f, t, tdb))
      {
        result.insert(f);
      }
    }
  }

  return std::vector<TNode>(result.cbegin(), result.cend());
}

bool ContextualEnumerator::isSymbolRelevant(TNode f, TNode t, TermDb* tdb)
{
  const Kind fKind = f.getKind();

  const Kind tKind = t.getKind();

  bool hasCtxtEnumAttr = true;
  f.getAttribute(CtxtEnumAttribute(), hasCtxtEnumAttr);

  return (tKind != Kind::APPLY_SELECTOR) && (tKind != Kind::APPLY_TESTER)
         && (tKind != Kind::APPLY_UF || fKind != Kind::SKOLEM)
         && !hasCtxtEnumAttr && tdb->isTermActive(t)
         && inst::TriggerTermInfo::isAtomicTrigger(t);
}

Node ContextualEnumerator::getPredicateForType(TypeNode type)
{
  if (d_typeToPredicate.find(type) == d_typeToPredicate.end())
  {
    NodeManager* nodeMgr = nodeManager();

    TypeNode predicateType =
        nodeMgr->mkFunctionType(type, nodeMgr->booleanType());

    Node predicate = NodeManager::mkDummySkolem("PE", predicateType);

    predicate.setAttribute(CtxtEnumAttribute(), true);

    d_typeToPredicate[type] = predicate;
  }

  return d_typeToPredicate.at(type);
}

std::vector<Node> ContextualEnumerator::enumerateTermsWithSygus(TNode f)
{
  // Suppose we have a function symbol 'f' with argument types 'T', 'U' and
  // result type 'V'.  We intend to construct a grammar that enumerates
  // f-applications.  The grammar's root non-terminal should be:
  //
  //     N_V ::= f(N_T, N_U)
  //
  // Here 'N_V', 'N_T', and 'N_U' are a non-terminals of type V, T, and U
  // respectively.  We'll use methods from the SygusGrammarCons class to create
  // grammars for T and U.  Cache the grammar for each argument type.  Don't
  // worry about any further sharing since it's probably an excessive
  // optimization.

  {  // Begin tracing code
    Trace("contextual-enumerator")
        << "enumerateTermsWithSygus(" << f << ")" << std::endl;
  }  // End tracing code

  // Prepare the map from argument types to their grammars.

  std::unordered_map<TypeNode, SygusGrammar> typeToGrammar;

  const TypeNode fType = f.getType();

  const std::vector<TypeNode> argTypes = fType.getArgTypes();

  for (auto typeIt = argTypes.cbegin(); typeIt != argTypes.cend(); ++typeIt)
  {
    TypeNode type = *typeIt;

    if (typeToGrammar.find(type) == typeToGrammar.end())
    {
      typeToGrammar.emplace(std::make_pair(
          type, SygusGrammarCons::mkDefaultGrammar(d_env, type, Node::null())));
    }
  }

  // We'll transform all argument grammars in the following manner.
  //
  // 1.  For all datatype-sorted non-terminals remove any rule with kind ITE or
  // APPLY_SELECTOR.
  //
  // 2.  For all other non-terminals remove all rules and replace with the 'any
  // constant' rule.

  for (auto entryIt = typeToGrammar.begin(); entryIt != typeToGrammar.end();
       entryIt++)
  {
    SygusGrammar& grammar = entryIt->second;

    // Collect all the rules that we need to remove from the grammar.

    std::vector<std::pair<TNode, TNode>> rulesToRemove;

    const std::vector<Node>& nonTerminals = grammar.getNtSyms();

    for (auto ntIt = nonTerminals.cbegin(); ntIt != nonTerminals.cend(); ++ntIt)
    {
      const Node nt = *ntIt;

      const bool ntIsDt = nt.getType().isDatatype();

      const std::vector<Node> rules = grammar.getRulesFor(nt);

      for (std::vector<Node>::const_iterator ruleIt = rules.cbegin();
           ruleIt != rules.cend();
           ++ruleIt)
      {
        const Node rule = *ruleIt;

        const Kind ruleKind = rule.getKind();

        if (!ntIsDt
            || (ruleKind == Kind::ITE || ruleKind == Kind::APPLY_SELECTOR))
        {
          rulesToRemove.emplace_back(nt, rule);
        }
      }
    }

    // Remove all the rules as intended.

    for (auto ntRuleIt = rulesToRemove.cbegin();
         ntRuleIt != rulesToRemove.cend();
         ntRuleIt++)
    {
      grammar.removeRule(ntRuleIt->first, ntRuleIt->second);
    }

    // For any non-terminal of non-datatype sort we add a single rule for each
    // ground term known to the term database.
    // Using 'addAnyConstant' instead will crash the solver when used with an
    // uninterpreted sort.

    addConstantRules(grammar);
  }

  // Isolate the root non-terminal for each argument's grammar.  For example, I
  // expect type T's grammar to have exactly one non-terminal of type T.  This
  // non-terminal is treated as the start non-terminal.

  std::unordered_map<TypeNode, TNode> typeToNonTerminal;

  for (auto entryIt = typeToGrammar.cbegin(); entryIt != typeToGrammar.cend();
       ++entryIt)
  {
    const TypeNode type = entryIt->first;

    const std::vector<Node>& nonTerminals = entryIt->second.getNtSyms();

    // Non-terminals in the grammar associated with 'type' that have type
    // 'type'.
    std::vector<Node> typeNonTerminals;

    std::copy_if(nonTerminals.begin(),
                 nonTerminals.end(),
                 std::back_inserter(typeNonTerminals),
                 [type](const TNode nonTerminal) {
                   return nonTerminal.getType() == type;
                 });

    Assert(typeNonTerminals.size() == 1);

    typeToNonTerminal[type] = typeNonTerminals.back();
  }

  // Manufacture the "root" non-terminal -- the one responsible for producing
  // all f-applications.

  const Node rootNonTerminal =
      NodeManager::mkDummySkolem("rootNonTerminal", fType.getRangeType());

  // Collect all the non-terminals -- all non-terminals across all argument
  // grammars as well as the non-terminal for the f-applications.  (Lead with
  // the non-terminal for f-applications!)

  std::vector<Node> allNonTerminals{rootNonTerminal};

  for (auto entryIt = typeToGrammar.cbegin(); entryIt != typeToGrammar.cend();
       ++entryIt)
  {
    const std::vector<Node>& typeNonTerminals = entryIt->second.getNtSyms();

    allNonTerminals.insert(allNonTerminals.end(),
                           typeNonTerminals.begin(),
                           typeNonTerminals.end());
  }

  // Use the master list of non-terminals to construct the root grammar.

  SygusGrammar rootGrammar(std::vector<Node>(), allNonTerminals);

  // Make the sole production rule for the root non-terminal.

  Node rootRule = makeRootRule(f, typeToNonTerminal);

  // Associate root_rule with root_nt in root_gr.

  rootGrammar.addRule(rootNonTerminal, rootRule);

  // Add all rules for all non-terminals across all argument grammars to the
  // root grammar.

  for (auto entryIt = typeToGrammar.begin(); entryIt != typeToGrammar.end();
       ++entryIt)
  {
    SygusGrammar& grammar = entryIt->second;

    const std::vector<Node>& nonTerminals = grammar.getNtSyms();

    for (auto nonTerminalIt = nonTerminals.cbegin();
         nonTerminalIt != nonTerminals.cend();
         ++nonTerminalIt)
    {
      const TNode nonTerminal = *nonTerminalIt;

      const std::vector<Node>& rules = grammar.getRulesFor(nonTerminal);

      for (auto ruleIt = rules.cbegin(); ruleIt != rules.cend(); ++ruleIt)
      {
        const TNode rule = *ruleIt;

        rootGrammar.addRule(nonTerminal, rule);
      }
    }
  }

  // Before we resolve the grammar let's make sure we have exactly what we need
  // by printing all its non-terminals and associated rules.

  {  // Begin tracing code
    Trace("contextual-enumerator")
        << "Grammar for operator " << f << " is:" << std::endl;

    debugPrintGrammar(rootGrammar, Trace("contextual-enumerator"));
  }  // End tracing code

  // We need to resolve the grammar, quitting early if resolution fails.

  const TypeNode& rootGrammarType = rootGrammar.resolve();

  Assert(rootGrammar.isResolved());

  // Declare the vector that we'll use to store the terms we generate.  Let's
  // also pre-emptively grab the maxium number of terms we will generate for
  // each function symbol.

  std::vector<Node> generatedTerms;

  const int64_t limit = options().quantifiers.contextualEnumeratorLimit;

  // Make an enumeration type to store our preference among the
  // SygusTermEnumerator and the SygusSampler.

  switch (options().quantifiers.contextualEnumeratorStrategy)
  {
    case options::ContextualEnumeratorStrategy::ENUMERATE:
    {
      SygusTermEnumerator rootGrammarEnumerator(d_env, rootGrammarType);

      // Let's keep going till either increment() returns false or we generate
      // contextualEnumeratorLimit-many terms.

      int64_t generatedTermCount = 0;

      // **Note**.  first_time should be false when n_gend_terms >= limit and
      // true otherwise.

      bool firstTime = generatedTermCount < limit;

      while (
          firstTime
          || (generatedTermCount < limit && rootGrammarEnumerator.increment()))
      {
        if (firstTime)
        {
          firstTime = false;
        }

        const Node current = rootGrammarEnumerator.getCurrent();

        if (!current.isNull())
        {
          generatedTerms.push_back(current);

          generatedTermCount++;
        }
      }

      break;
    }

    case options::ContextualEnumeratorStrategy::SAMPLE:
    {
      // To start with we construct and initialize the sampler.

      SygusSampler rootGrammarSampler = SygusSampler(d_env);

      const Node rootGrammarVar =
          NodeManager::mkDummySkolem("sampler_", rootGrammarType);

      rootGrammarSampler.initialize(
          rootGrammarType, std::vector<Node>{rootGrammarVar}, limit);

      // We *requested* limit-many points but actually generated
      // n_sample_pts-many points.

      const size_t sampleSize = rootGrammarSampler.getNumSamplePoints();

      for (size_t i = 0; i < sampleSize; i++)
      {
        const std::vector<Node>& samplePoint =
            rootGrammarSampler.getSamplePoint(i);

        // We've requested only one term because the vector we passed to
        // initialize has length exactly 1.  We'll error out if we have any more
        // or any less terms.

        Assert(samplePoint.size() == 1);

        // At this point we're sure that sample_pt contains exactly one term.
        // This is a SyGuS term.  However we want the term it represents,
        // otherwise known as a builtin term.

        generatedTerms.push_back(d_treg.getTermDatabaseSygus()->sygusToBuiltin(
            samplePoint.back(), rootGrammarType));
      }

      break;
    }
  }

  // Let's return the terms that we have generated using the grammar.

  return generatedTerms;
}

void ContextualEnumerator::addConstantRules(SygusGrammar& grammar)
{
  TermDb* termDatabase = getTermDatabase();

  const std::vector<Node>& nonTerminals = grammar.getNtSyms();

  for (std::vector<Node>::const_iterator nonTerminalIt = nonTerminals.cbegin();
       nonTerminalIt != nonTerminals.cend();
       ++nonTerminalIt)
  {
    const TNode nonTerminal = *nonTerminalIt;

    const TypeNode type = nonTerminal.getType();

    if (!type.isDatatype())
    {
      Assert(grammar.getRulesFor(nonTerminal).empty());

      const size_t groundTermCount = termDatabase->getNumTypeGroundTerms(type);

      for (size_t i = 0; i < groundTermCount; ++i)
      {
        const TNode groundTerm = termDatabase->getTypeGroundTerm(type, i);

        grammar.addRule(nonTerminal, groundTerm);
      }

      if (groundTermCount == 0)
      {
        grammar.addRule(nonTerminal,
                        termDatabase->getOrMakeTypeGroundTerm(type));
      }
    }

    Assert(!grammar.getRulesFor(nonTerminal).empty());
  }
}

Node ContextualEnumerator::makeRootRule(
    const TNode f, const std::unordered_map<TypeNode, TNode>& typeToNonTerminal)
{
  const TNode t = getTermDatabase()->getOrMkDbListForOp(f)->d_list[0];

  std::vector<TNode> children;

  if (t.getMetaKind() == kind::MetaKind::PARAMETERIZED)
  {
    children.push_back(f);
  }

  std::vector<TypeNode> argTypes = f.getType().getArgTypes();

  for (auto typeIt = argTypes.cbegin(); typeIt != argTypes.cend(); ++typeIt)
  {
    children.push_back(typeToNonTerminal.at(*typeIt));
  }

  return nodeManager()->mkNode(t.getKind(), children);
}

void ContextualEnumerator::debugPrintGrammar(const SygusGrammar& grammar,
                                             std::ostream& out)
{
  const std::vector<Node>& nonTerminals = grammar.getNtSyms();

  std::for_each(nonTerminals.cbegin(),
                nonTerminals.cend(),
                [grammar, &out](const TNode nt) {
                  const std::vector<Node>& rules = grammar.getRulesFor(nt);
                  std::for_each(
                      rules.cbegin(), rules.cend(), [nt, &out](const TNode r) {
                        out << "* " << nt << " --> " << r << std::endl;
                      });
                });
}
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
