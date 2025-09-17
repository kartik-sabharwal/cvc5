#include "theory/quantifiers/symbolic_evaluator.h"
#include "theory/quantifiers/first_order_model.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SymbolicEvaluator::SymbolicEvaluator(Env& env,
                                     QuantifiersState& qs,
                                     QuantifiersInferenceManager& qim,
                                     QuantifiersRegistry& qr,
                                     TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_evaluator(env, qs)
{
  d_set_up_evaluator = false;
  d_round = 0;
}
SymbolicEvaluator::~SymbolicEvaluator() {}
bool SymbolicEvaluator::needsCheck(Theory::Effort e)
{
  return d_qstate.getInstWhenNeedsCheck(e);
}
void SymbolicEvaluator::reset_round(Theory::Effort e) {}
void SymbolicEvaluator::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e != QEFFORT_STANDARD)
  {
    return;
  }

  ++d_round;

  if (!d_set_up_evaluator)
  {
    setUpEvaluator();
  }
  
  Trace("SymbolicEvaluator") << "(round)" << std::endl;

  if (d_round == 3)
  {
    Trace("SymbolicEvaluator") << getEqualityEngine()->debugPrintEqc();

    printPlusTerms();
  }
}
/**
 * Say we want to print all the terms in the database that have the function
 * symbol plus as their operator.  Before doing anything else we will fetch the
 * current term database.  First we need to search through the list of all
 * operators till we find an operator with the name plus.  We will use
 * getNumOperators() and getOperator() to find the right operator.  If we don't
 * find it we'll simply return from the function.  Once we find the function we
 * will use getOrMkDbListForOp() to retrieve all terms that have plus as their
 * operator.  Once we have an instance of DbList we can extract a CDList<Node>
 * from it and subsequently iterate over its elements.
 */
void SymbolicEvaluator::printPlusTerms()
{
  Cvc5ostream out = Trace("SymbolicEvaluator");
  TermDb* tdb = getTermDatabase();
  TNode plus = Node::null();
  const size_t n_ops = tdb->getNumOperators();
  for (size_t i = 0; i < n_ops; ++i)
  {
    TNode op = tdb->getOperator(i);
    if (op.getName() == "plus")
    {
      plus = op;
      break;
    }
  }
  if (plus.isNull())
  {
    out << "Couldn't find an operator named plus." << std::endl;
    return;
  }
  DbList* terms = tdb->getOrMkDbListForOp(plus);
  std::vector<Node>::const_iterator it = terms->d_list.begin();
  const std::vector<Node>::const_iterator terms_end = terms->d_list.end();
  const uint64_t fuel = options().quantifiers.symbolicEvaluatorFuel;
  for (; it != terms_end; ++it)
  {
    const Node in_term = *it;
    const Node out_term =
        d_evaluator.evaluateDefinitionsSymbolically(*it, fuel);
    out << "(--> " << in_term << " " << out_term << ")" << std::endl;
    // break; // Quit after evaluating the first term in the list.
  }
}
/**
 * We begin by fetching the asserted universally quantified formulas.  To do
 * this we need to consult the current first-order model (d_treg.getModel()),
 * grab from it the number of asserted universally quantified formulas
 * (getNumAssertedQuantifiers()), go over the formulas
 * (getAssertedQuantifier()), assert it to the FunDefEvaluator instance
 * (assertDefinition()).  If it's not a definition the call will return false,
 * which we can ignore, otherwise it will return true.
 */
void SymbolicEvaluator::setUpEvaluator()
{
  FirstOrderModel* fom = d_treg.getModel();
  Cvc5ostream out = Trace("SymbolicEvaluator");
  out << "(loaded";
  const size_t n_asserted = fom->getNumAssertedQuantifiers();
  for (size_t i = 0; i < n_asserted; ++i)
  {
    TNode phi = fom->getAssertedQuantifier(i);
    if (d_evaluator.assertDefinition(phi))
    {
      out << " " << QuantAttributes::getFunDefHead(phi);
    }
  }
  out << ")" << std::endl;
  d_set_up_evaluator = true;
}
std::string SymbolicEvaluator::identify() const { return "symbolic-evaluator"; }

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
