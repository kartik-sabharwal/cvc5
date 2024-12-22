#include "theory/quantifiers/my_quantifiers_module.h"

#include "expr/node_traversal.h"
#include "expr/skolem_manager.h"
#include "theory/quantifiers/ematching/trigger_term_info.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/skolemize.h"
#include "theory/quantifiers/sygus_sampler.h"
#include "theory/quantifiers/term_enumeration.h"

#include <stack>

/* What are we trying to do here?
 *
 * 1. collect all sorts in the current signature,
 * 2. declare an enumeration predicate for each of these sorts,
 * 3. collect all the equivalence classes in the current signature,
 * 4. find out which equivalence classes contain **concrete** terms,
 * 5. iterate over all equalities in the equivalence class of false and gather
 * the ones where either the LHS or RHS cannot be equated to a concrete term,
 * (what if we want to consider only equalities where **neither** LHS nor RHS
 * can be equated to a constant term?)
 * 6. remove equalities that can be refuted by counterexamples,
 * 7. pair up terms in equivalence classes of LHS and terms in equivalence
 * classes of RHS to create lemma candidates,
 * 8. eliminate destructors in lemma candidates,
 * 9. if a term appears in both the LHS and RHS of a lemma candidate, replace
 * it with a new variable and generalize it away,
 * 10. add the appropriate universal quantifiers to get 'real' lemmas,
 * 11. prompt the user for a particular lemma,
 * 12. submit the lemma to the solver.
 */

/* IDEAS:
 *
 * 1. Eliminate lemmas candidates that are propositional consequences using
 * your own partial evaluator or using a subsolver. Essentially you want to
 * eliminate possibilities that are entailed deductively (as opposed to
 * entailed inductively)
 */

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

MyQuantifiersModule::MyQuantifiersModule(Env& env, QuantifiersState& qs,
  QuantifiersInferenceManager& qim, QuantifiersRegistry& qr,
  TermRegistry& tr)
  : QuantifiersModule(env, qs, qim, qr, tr) 
{
  d_stashed = false;
}

MyQuantifiersModule::~MyQuantifiersModule() 
{
}

bool MyQuantifiersModule::needsCheck(Theory::Effort e) 
{
  // @Kartik. Use exactly the same implementation as
  // ConjectureGenerator::needsCheck as suggested by Andy.
  // Apparently this ensures that MyQuantifiersModule sends lemmas
  // 'at the same time' as ConjectureGenerator.
  return d_qstate.getInstWhenNeedsCheck(e);
}

void MyQuantifiersModule::reset_round(Theory::Effort e) 
{
}

void MyQuantifiersModule::check(Theory::Effort e, QEffort quant_e) 
{
  // @Kartik.  ConjectureGenerator::check does work only if quant_e
  // equals QEFFORT_STANDARD.
  // We want to match that behavior here.
  if ( quant_e != QEFFORT_STANDARD )
  {
    return;
  }

  std::cout << std::endl << std::endl << "***** check *****" << std::endl;
  // std::cout << getEqualityEngine()->debugPrintEqc() << std::endl;
  clearFields();
  populateTypes();
  populateDummyPredicates();
  collectEquivalenceClasses();
  buildOperatorArgumentIndices();
  mapEquivalenceClassesToGroundTerms();
  partitionEquivalenceClasses();
  std::cout << std::endl << "** current assumptions **" << std::endl;
  // showCurrentAssumptions();
  collectRelevantInequations();
  std::cout << std::endl << "** after relevance filtering **" << std::endl;
  showRelevantInequations();
  filterRelevantInequationsBySampling();
  std::cout << std::endl << "** after counterexample filtering **" << std::endl;
  showRelevantInequations();
  collectLemmaCandidates();
  std::cout << std::endl << "** lemma candidates **" << std::endl;
  showLemmaCandidates();
  showConcreteLemmaCandidates();
  // exit(0);
  // printGroundTermsEquivalentToSubterms();
  // eliminateDestructorsInLemmaCandidates();
  // generalizeLemmaCandidates();
  // std::cout << std::endl << "** after destructor elimination **" << std::endl;
  // showLemmaCandidates();
  // bindVarsInLemmas();
  // std::cout << std::endl << "** after generalization **" << std::endl;
  // showLemmaCandidates();
  // promptForLemma();
  return;
}

void MyQuantifiersModule::clearFields() 
{
  d_eqcs.clear();
  d_rel_eqcs.clear();
  d_irrel_eqcs.clear();
  d_ground_eqc_map.clear();
  d_op_arg_indices.clear();
  d_rel_ineqns.clear();
  d_lemma_cands.clear();
  d_types.clear();
}

void MyQuantifiersModule::collectEquivalenceClasses()
{
  for ( eq::EqClassesIterator eqc_it = 
          eq::EqClassesIterator(getEqualityEngine());
        !eqc_it.isFinished();
        eqc_it++ ) 
  {
    Node eqc = *eqc_it;
    d_eqcs.push_back(eqc);
  }

  return;
}

void MyQuantifiersModule::showEquivalenceClasses()
{
  for (auto representative : d_eqcs) 
  {
    std::cout << representative << " = {";
    bool first_element = true;
    for ( eq::EqClassIterator term =
            eq::EqClassIterator(representative, getEqualityEngine());
          !term.isFinished();
          term++ )
    {
      if ( first_element )
      {
        first_element = false;
      } else 
      {
        std::cout << ", ";
      }
      std::cout << *term;
    }
    std::cout << "}" << std::endl;
  }
}

void MyQuantifiersModule::buildOperatorArgumentIndices()
{
  for ( Node eqc : d_eqcs ) 
  {
    for ( eq::EqClassIterator term_it =
            eq::EqClassIterator(eqc, getEqualityEngine());
          !term_it.isFinished();
          term_it++ )
    {
      Node term = *term_it;

      // TERM is *handled* when it is:
      // - an application of a non-skolem uninterpreted function, or
      // - an application of a tester, or
      // - an application of a selector, or
      // - an application of some set of theory primitives.
      //
      // This is because TERM needs to be an *atomic trigger*, which
      // precludes the possibility of it being a constant.
      // Terms that are applications of uninterpreted functions, or
      // of selectors, or testers, or the aforementioned theory primitives
      // are all atomic triggers.
      //
      // TERM also needs to be *active*, which means one of its arguments
      // must be active (a Skolemization of a datatype-sorted bound
      // variable that was in its own equivalence class when it was
      // introduced, or an operator with at least one active argument.)
      if ( getTermDatabase()->hasTermCurrent(term) &&
           isHandledTerm(term) ) 
      {
        // TERM necessarily has an operator and one or more operands.
        // CHILD_EQCS[i] is intended to be the representative of TERM[i]'s
        // equivalence class.
        std::vector<Node> child_eqcs;
        
        for ( const Node& child : term ) 
        {
          child_eqcs.push_back(d_qstate.getRepresentative(child));
        }
        
        // Suppose TERM has the form:
        //     f(a1, a2)
        // Say a1 is in the equivalence class of representative r1, and a2 is
        // in the equivalence class of representative r2.
        // We want to notify the operator-argument index that there is a way
        // to construct a term equivalent to EQC like:
        //     f(r1, r2)
        MyOpArgIndex& op_arg_index = d_op_arg_indices[eqc];

        addTerm(op_arg_index, child_eqcs, term);
      }
    }
  }
}

bool MyQuantifiersModule::isHandledTerm(Node n) 
{
  return getTermDatabase()->isTermActive(n) &&
    inst::TriggerTermInfo::isAtomicTrigger(n) &&
    ( n.getKind() != Kind::APPLY_UF ||
      n.getOperator().getKind() != Kind::SKOLEM );
}

void MyQuantifiersModule::addTerm(MyOpArgIndex& root_op_arg_index,
                                  std::vector<Node> args,
                                  Node term) 
{
  using std::endl;
  using std::stack;
  using std::reference_wrapper;
  using std::find;
  using std::vector;
  using std::map;

  unsigned i = 0;
  
  stack<reference_wrapper<MyOpArgIndex>> cont;
  cont.push(root_op_arg_index);

  while ( !cont.empty() ) 
  {
    MyOpArgIndex& op_arg_index = cont.top().get();
    cont.pop();
    
    if ( i == term.getNumChildren() ) 
    {
      Node op = term.getOperator();

      vector<Node>& ops = op_arg_index.d_ops;

      vector<Node>::iterator it = find(ops.begin(), ops.end(), op);

      if ( it == ops.end() ) 
      {
        vector<Node>& op_terms = op_arg_index.d_op_terms;

        ops.push_back(op);
        op_terms.push_back(term);
      }
    } else 
    {
      map<Node, MyOpArgIndex>& children = op_arg_index.d_children;

      MyOpArgIndex& child_op_arg_index = children[args[i]];

      cont.push(child_op_arg_index);

      i++;
    }
  }
}

void MyQuantifiersModule::showOpArgIndices() 
{
  using std::pair;
  using std::tuple;
  using std::stack;
  using std::string;
  using std::get;
  using std::endl;

  typedef unsigned Indent;
  typedef tuple<Node, MyOpArgIndex, Indent> Job;

  stack<Job> cont;

  for ( auto entry : d_op_arg_indices ) 
  {
    cont.push({entry.first, entry.second, 0});
  }

  while ( !cont.empty() )
  {
    Job job = cont.top();
    cont.pop();

    string label = get<0>(job).toString();
    MyOpArgIndex op_arg_index = get<1>(job);
    Indent indent = get<2>(job);

    {
      string spaces(indent, ' ');
      std::cout << spaces << label << "(" <<
        op_arg_index.d_ops.size() << ") => " << std::endl;
    }

    Indent new_indent = indent + 2;

    std::vector<Node> ops = op_arg_index.d_ops;
    std::vector<Node> op_terms = op_arg_index.d_op_terms;

    for ( size_t i = 0; i < ops.size(); i++ ) 
    {
      string spaces(new_indent, ' ');
      std::cout << spaces << ops[i] << " with " << op_terms[i] << std::endl;
    }

    for ( pair<Node, MyOpArgIndex> entry : op_arg_index.d_children ) 
    {
      cont.push({entry.first, entry.second, new_indent});
    }
  }

  std::cout << std::endl;

  return;   
}

void MyQuantifiersModule::mapEquivalenceClassesToGroundTerms() 
{
  // If EQC is has sort Bool, it must be equal to either true or false.
  // In this case, we do not need to search for a ground term for EQC,
  // we set EQC's ground term in D_GROUND_EQC_MAP to EQC itself.
  for (Node eqc : d_eqcs) 
  {
    if (eqc.getType().isBoolean())
    {
      d_ground_eqc_map[eqc] = eqc;
    }
  }

  // If EQC in D_EQCS is of an inductive datatype sort, we attempt to use
  // D_OP_ARG_INDEX to construct a ground term equivalent to EQC.
  //
  // In case we succeed and produce a ground term T equivalent to EQC,
  // we map EQC to T in D_GROUND_EQC_MAP.
  //
  // The attempt may fail for two reasons -- either it is genuinely impossible
  // to construct a ground term equivalent to EQC, or that across all the
  // ways to construct a (ground or otherwise) term equivalent to EQC, there
  // is at least one argument whose equivalence class we have not visited so
  // far, and therefore we aren't aware the argument is equivalent to a ground
  // term.
  //
  // Since we want to avoid the latter kind of failure, we repeatedly loop
  // over all equivalence classes until we hit a fixed point. In other words,
  // if in a particular loop we find that no new entries have been added to
  // D_GROUND_EQC_MAP, we reason that we have reached a fixed point and do not
  // loop over the equivalence classes again.
  //
  // This 'repeated looping' is the reason we have a 'for' loop within a
  // 'do-while' loop. The 'for' loop iterates over the equivalence class
  // representatives, and the 'do-while' loop iterates till we hit a fixed
  // point.
  // 
  // If EQC is not of an inductive datatype sort, we choose not to work so
  // hard, and we map EQC to itself in D_GROUND_EQC_MAP.
  bool fixed_point;

  do 
  {
    // We start by assuming we have reached a fixed point, we will set this to
    // false if we manage to add a new entry to D_GROUND_EQC_MAP.
    fixed_point = true;

    for ( Node eqc : d_eqcs ) 
    {
      if ( eqc.isNull() ) 
      { 
        continue;
      }

      if ( d_ground_eqc_map.find(eqc) == d_ground_eqc_map.end() ) 
      {
        if ( Skolemize::isInductionTerm(options(), eqc) ) 
        {
          Node term = getGroundTerm(d_op_arg_indices[eqc]);
          
          if ( !term.isNull() ) 
          {
            d_ground_eqc_map[eqc] = term;

            fixed_point = false;
          }
        } else 
        {
          d_ground_eqc_map[eqc] = eqc;

          fixed_point = false;
        }
      }
    }
  } while ( !fixed_point );
}

Node MyQuantifiersModule::getGroundTerm(MyOpArgIndex& root_op_arg_index) 
{
  using std::tuple;
  using std::vector;
  using std::map;
  using std::stack;
  using std::reference_wrapper;
  using std::get;
  using std::next;

  enum Command { TryDescent, Ascend };
  typedef map<Node, MyOpArgIndex>::iterator Cursor;
  typedef reference_wrapper<MyOpArgIndex> OpArgIndexRef;
  typedef tuple<Command, OpArgIndexRef, Cursor, Cursor> Job;

  Node result = Node::null();
  vector<Node> arguments;
  stack<Job> continuation;
  continuation.push({TryDescent,
      root_op_arg_index,
      root_op_arg_index.d_children.begin(),
      root_op_arg_index.d_children.end()});

  while ( !continuation.empty() )
  {

    Job job = continuation.top();
    continuation.pop();

    Command command = get<0>(job);
    OpArgIndexRef op_arg_index = get<1>(job);
    Cursor current = get<2>(job);
    Cursor limit = get<3>(job);

    if ( command == TryDescent &&
         !op_arg_index.get().d_ops.empty() )
    {
      vector<Node> children = { op_arg_index.get().d_ops[0] };
      children.insert(children.end(), arguments.begin(), arguments.end());
      result =
        NodeManager::currentNM()->mkNode(
          op_arg_index.get().d_op_terms[0].getKind(),
          children);

    } else if ( command == TryDescent &&
                op_arg_index.get().d_ops.empty() &&
                current == limit ) 
    {
      result = Node::null();

    } else if ( command == TryDescent &&
                op_arg_index.get().d_ops.empty() &&
                current != limit &&
                d_ground_eqc_map.find(current->first) ==
                  d_ground_eqc_map.end() ) 
    {
      continuation.push({TryDescent, op_arg_index, next(current), limit});

    } else if ( command == TryDescent &&
                op_arg_index.get().d_ops.empty() &&
                current != limit &&
                d_ground_eqc_map.find(current->first) !=
                  d_ground_eqc_map.end() )
    {

      arguments.push_back(current->first);

      continuation.push({Ascend, op_arg_index, current, limit});

      continuation.push({TryDescent,
          current->second,
          (current->second).d_children.begin(),
          (current->second).d_children.end()});

    } else if ( command == Ascend && result.isNull() )
    {

      arguments.pop_back();

      continuation.push({TryDescent, op_arg_index, next(current), limit});

    } else 
    {
      Assert( command == Ascend );
      Assert( !result.isNull() );

      arguments.pop_back();
    }
  }

  return result;
}

void MyQuantifiersModule::showGroundTermsForEquivalenceClasses() 
{
  for ( Node representative : d_eqcs ) 
  {
    if ( d_ground_eqc_map.find(representative) != d_ground_eqc_map.end() )
    {
      std::cout << "Representative " << representative <<
        " is associated with the ground term " <<
        d_ground_eqc_map[representative] << std::endl;
    }
    else 
    {
      std::cout << "Representative " << representative <<
        " is not associated with a ground term." << std::endl;
    }
  }
  return;
}

std::string MyQuantifiersModule::identify() const
{
  return "my-quantifiers-module";
}

void MyQuantifiersModule::partitionEquivalenceClasses()
{
  /* Populate D_GROUND_REL_EQCS and D_GROUNDED_EQCS by partitioning D_EQCS.
   * 
   * For EQC in D_EQCS, if EQC is associated with a value in D_GROUND_EQC_MAP,
   * then it is placed in D_GROUNDED_EQCS. Otherwise it is placed in
   * D_GROUND_REL_EQCS.
   */
  for ( Node eqc : d_eqcs ) 
  {
    if ( d_ground_eqc_map.find(eqc) == d_ground_eqc_map.end() ) 
    {
      d_rel_eqcs.push_back(eqc);
    }
    else 
    {
      d_irrel_eqcs.push_back(eqc);
    }
  }
  return;
}

void MyQuantifiersModule::showFalsifiedEqualities() 
{
  eq::EqualityEngine* ee = getEqualityEngine();

  Node false_node = NodeManager::currentNM()->mkConst(false);

  eq::EqClassIterator false_iterator =
    eq::EqClassIterator(false_node, ee);

  while ( !false_iterator.isFinished() ) {
    Node false_term = *false_iterator;
    if ( false_term.getKind() == Kind::EQUAL )
    {
      std::cout << false_term << " is an equality falsified in the current model." << std::endl;
    }
    false_iterator++;
  }
}

void MyQuantifiersModule::showAssertedForalls()
{ 
  quantifiers::FirstOrderModel* model = d_treg.getModel();

  for ( size_t i = 0; i < model->getNumAssertedQuantifiers(); i++ )
  {
    std::cout << "Asserted quantifier #" << i << " is " <<
      model->getAssertedQuantifier(i) << std::endl;
  }    
}

void MyQuantifiersModule::showCurrentAssumptions() {
  eq::EqualityEngine* ee = getEqualityEngine();

  for ( eq::EqClassIterator assumption_cursor = 
          eq::EqClassIterator(NodeManager::currentNM()->mkConst(true), ee);
        !assumption_cursor.isFinished();
        assumption_cursor++ ) {
    Node assumption = *assumption_cursor;
    std::cout << "- " << assumption << std::endl;
  }
}

void MyQuantifiersModule::collectRelevantInequations() 
{
  eq::EqualityEngine* ee = getEqualityEngine();
    
  for ( eq::EqClassIterator goal_cursor = 
          eq::EqClassIterator(NodeManager::currentNM()->mkConst(false), ee);
        !goal_cursor.isFinished();
        goal_cursor++ )
  {
    Node goal = *goal_cursor;
    
    if ( goal.getKind() == Kind::EQUAL )
    {
      for ( size_t i = 0; i < 2; i++ )
      {
        if ( std::find(d_rel_eqcs.begin(), d_rel_eqcs.end(), 
               ee->getRepresentative(goal[i])) != d_rel_eqcs.end() )
        {
          if ( std::find(d_rel_ineqns.begin(), d_rel_ineqns.end(), goal) ==
                 d_rel_ineqns.end() )
          {
            d_rel_ineqns.push_back(goal);
          }
        }
      }
    }
  }

  return;
}

void MyQuantifiersModule::collectSkolemVariablesInTerm(
  Node term, std::vector<Node>& sk_vars)
{
  std::vector<Node> continuation;
  continuation.push_back(term);

  while ( !continuation.empty() )
  {
    Node next_term = continuation.back();
    continuation.pop_back();

    if ( next_term.isConst() )
    {
      continue;
    }
    else if ( next_term.isVar() )
    {
      if ( std::find(sk_vars.begin(), sk_vars.end(), next_term) ==
             sk_vars.end() )
      {
        sk_vars.push_back(next_term);
      }
    }
    else if ( next_term.hasOperator() )
    {
      for ( auto child_term : next_term ) 
      {
        continuation.push_back(child_term);
      }
    }
    else 
    {
      Assert(false);
    }
  }
}

void MyQuantifiersModule::showLemmaCandidates()
{
  for ( size_t i = 0; i < d_rel_ineqns.size(); i++ )
  {
    Node eqn = d_rel_ineqns[i];

    std::cout << "[GOAL] " << i << ". " << eqn << " :" << std::endl;

    for ( size_t j = 0; j < d_lemma_cands[i].size(); j++ )
    {
      std::cout << "    [LEMMA] " << j << ". " << d_lemma_cands[i][j] << 
        std::endl;
    }
  }

  return;

  // std::vector<Node> sk_vars;
  // collectSkolemVariablesInTerm(lemma_lhs, sk_vars);
  // collectSkolemVariablesInTerm(lemma_rhs, sk_vars);
  // std::vector<std::vector<Node>> substn_imgs;
  // generateSubstitutionImages(10, sk_vars, substn_imgs);
  // for ( auto substn_img : substn_imgs ) {
  //   Node concrete_lhs = 
  //     d_env.evaluate(lemma_lhs, sk_vars, substn_img, true);
  //   Node concrete_rhs =
  //     d_env.evaluate(lemma_rhs, sk_vars, substn_img, true);

  //   for ( auto concrete_term : 
  //           std::vector<Node>{ concrete_lhs, concrete_rhs } )
  //   {
  //     if ( !ee->hasTerm(concrete_term) )
  //     {
  //       ee->addTerm(concrete_term);
  //       getTermDatabase()->addTerm(concrete_term);
  //     }
  //   }

  //   std::cout << "    - " << concrete_lhs << " = " << concrete_rhs << 
  //     "[" << ee->areEqual(concrete_lhs, concrete_rhs) <<  "]" << 
  //     std::endl;
  // }
          
  // for ( auto substn_img : substn_imgs )
  // {
  //   std::cout << "    - {";
  //   bool first = true;
  //   for ( size_t i = 0; i < sk_vars.size(); i++ )
  //   {
  //     if ( first )
  //     {
  //       first = false;
  //     }
  //     else
  //     {
  //       std::cout << ", ";
  //     }
  //     std::cout << sk_vars[i] << " := " << substn_img[i];
  //   }
  //   std::cout << "}" << std::endl;
  // }
}

void MyQuantifiersModule::generateSubstitutionImages(
  size_t limit, std::vector<Node>& sk_vars, 
  std::vector<std::vector<Node>>& substn_imgs)
{
  size_t arity = sk_vars.size();

  if (arity > 0) 
  {
    TermEnumeration* term_enum = d_treg.getTermEnumeration();

    std::vector<int> config;
    for ( size_t i = 0; i < arity; i++ )
    {
      config.push_back(0);
    }

    std::vector<TypeNode> types;
    for ( auto sk_var : sk_vars )
    {
      TypeNode type_ = sk_var.getType();
      if ( type_.isClosedEnumerable() )
      {
        types.push_back(type_);
      }
      else
      {
        return;
      }
    }

    config.pop_back();
    int config_size = 0;
    int prefix_size = -1;
    unsigned i = 0;
    unsigned prev_count = substn_imgs.size();

    while ( substn_imgs.size() < limit )
    {
      if (prefix_size == -1) 
      {
        prefix_size = 0;
        config.push_back(config_size);
      } 
      else if ( i < config.size() &&
                prefix_size < config_size &&
                !term_enum->getEnumerateTerm(
                   types[i], config[i] + 1).isNull() )
      {
        /* We have already checked that (CONFIG[i] + 1) is a good index for
         * TYPE[i]'s enumeration list. */
        config[i] = config[i] + 1;
        prefix_size++;
        config.push_back(config_size - prefix_size);

      } else if ( i < config.size() &&
                  (prefix_size >= config_size ||
                   term_enum->getEnumerateTerm(
                     types[i], config[i] + 1).isNull()) ) 
      {
        prefix_size -= config[i];
        config[i] = 0;
        i++;
      } 
      else 
      {
        // std::cout << "i = " << i << ", config.size() = " << config.size() <<
        //   ", config_size = " << config_size << ", prefix_size = " <<
        //   prefix_size << ", substn_imgs.size() = " << substn_imgs.size() <<
        //   std::endl;
        // Assert(false);
      }

      if ( i < config.size() && config.size() == arity )
      {
        /* We have not checked whether config[arity - 1] is a legal index!
         * However we know config[0] through config[arity - 2] are legal
         * indices.
         * Let's check config[arity - 1] as well before we construct the
         * term. */
        Node last_child = term_enum->getEnumerateTerm(
                            types[arity - 1], config[arity - 1]);

        if ( !last_child.isNull() ) 
        {
          substn_imgs.push_back(std::vector<Node>{});
          std::vector<Node>& substn_img = substn_imgs.back();

          /* J stops at (ARITY - 1) since we already have LAST_CHILD. */
          for (size_t j = 0; j < arity - 1; j++) {
            Node jth_child = term_enum->getEnumerateTerm(types[j], config[j]);
            substn_img.push_back(jth_child);
          }

          substn_img.push_back(last_child);
        }

        config.pop_back();

        i = 0;
      } 
      else if ( i >= config.size() && substn_imgs.size() > prev_count ) 
      {
        prev_count = substn_imgs.size();
        config_size++;
        for ( size_t j = 0; j < config.size(); j++ ) 
        {
          config[j] = 0;
        }
        prefix_size = -1;
      } 
      else if ( i >= config.size() && substn_imgs.size() <= prev_count )
      {
        return;
      } 
      else 
      {
        // Assert(false);
      }
    }
  }

  return;
}

void MyQuantifiersModule::showRelevantInequations() 
{
  // std::cout << "The current goal alternatives are:" << 
  //  std::endl;
  for ( Node rel_ineqn : d_rel_ineqns )  
  {
    std::cout << " - " << rel_ineqn << std::endl;
  }
  return;
}

void MyQuantifiersModule::collectLemmaCandidates()
{
  eq::EqualityEngine* ee = getEqualityEngine();

  for ( size_t i = 0; i < d_rel_ineqns.size(); i++ )
  {
    d_lemma_cands.push_back(std::vector<Node>{});

    Node ineqn = d_rel_ineqns[i];

    std::vector<Node>& ineqn_lemma_cands = d_lemma_cands.back();

    for ( eq::EqClassIterator lhs_iter = 
            eq::EqClassIterator(ee->getRepresentative(ineqn[0]), ee);
          !lhs_iter.isFinished();
          lhs_iter++ )
    {
      for ( eq::EqClassIterator rhs_iter =
              eq::EqClassIterator(ee->getRepresentative(ineqn[1]), ee);
            !rhs_iter.isFinished();
            rhs_iter++ )
      {
        if ( ineqn[0] != *lhs_iter || ineqn[1] != *rhs_iter )
        {
          ineqn_lemma_cands.push_back(
            NodeManager::currentNM()->mkNode(
              Kind::EQUAL, *lhs_iter, *rhs_iter));
        }
      }
    }
  }
}

Node MyQuantifiersModule::eliminateDestructors(Node eqn)
{
  std::map<TypeNode, size_t> next_var;
  std::pair<Node, Node> substn = findDestructorApplication(eqn, next_var);
  while ( !substn.first.isNull() )
  {
    eqn = 
      evaluate(
        eqn,
        std::vector<Node>{ substn.first },
        std::vector<Node>{ substn.second },
        true);

    substn = findDestructorApplication(eqn, next_var);
  }

  return eqn;
}

std::pair<Node, Node> MyQuantifiersModule::findDestructorApplication(
  Node root_term, std::map<TypeNode, size_t>& next_var)
{
  std::vector<Node> continuation;
  continuation.push_back(root_term);

  while ( !continuation.empty() )
  {
    Node term = continuation.back();
    continuation.pop_back();

    if ( term.getKind() == Kind::APPLY_SELECTOR &&
         term[0].isVar() )
    {
      Node sel = term.getOperator();
      const DType& dt = sel.getType()[0].getDType();
      Node constr = findConstructorBySelector(sel, dt);
      std::vector<TypeNode> child_types = constr.getType().getArgTypes();
      std::vector<Node> children = { constr };

      for ( size_t i = 0; i < child_types.size(); i++ )
      {
        TypeNode type_ = child_types[i];
        
        if ( next_var.find(type_) == next_var.end() )
        {
          next_var[type_] = 0;
        }
   
        children.push_back(
          d_termCanon.getCanonicalFreeVar(type_, next_var[type_]));
  
        next_var[type_] = next_var[type_] + 1;
      } 

      return std::make_pair(
        term[0], 
        NodeManager::currentNM()->mkNode(
          Kind::APPLY_CONSTRUCTOR,
          children));
    }
    else if ( term.hasOperator() )
    {
      for ( auto child : term )
      {
        continuation.push_back(child);
      }
    }
    else 
    {
      Assert( term.isConst() || term.isVar() );
    }
  }

  return std::make_pair(Node::null(), Node::null());
}

void MyQuantifiersModule::populateTypes()
{
  TermDb* tdb = getTermDatabase();

  for ( size_t i = 0; i < tdb->getNumOperators(); i++ )
  {
    Node op = tdb->getOperator(i);

    TypeNode op_type = op.getType();

    if ( op_type.isFunctionLike() )
    {
      for ( auto op_type_child : op_type )
      {
        if ( std::find(d_types.begin(), d_types.end(), op_type_child) ==
               d_types.end() )
        {
          d_types.push_back(op_type_child);
        }
      }
    }
    else
    {
      if ( std::find(d_types.begin(), d_types.end(), op_type) ==
             d_types.end() )
      {
        d_types.push_back(op_type);
      }
    }
  }

  return;
}

void MyQuantifiersModule::showTypes()
{
  bool first_time = true;
  std::cout << "{";
  for ( auto type_ : d_types )
  {
    if ( first_time )
    {
      first_time = false;
    }
    else
    {
      std::cout << ", ";
    }
    std::cout << type_;
  }
  std::cout << "}" << std::endl;
}

Node MyQuantifiersModule::findOperatorByName(const std::string& name)
{
  TermDb* tdb = getTermDatabase();
  
  for ( size_t i = 0; i < tdb->getNumOperators(); i++ )
  {
    Node op = tdb->getOperator(i);
    if ( op.hasOperator() )
    {
      op = op.getOperator();
    }

    if ( op.hasName() && op.getName() == name )
    {
      return op;
    }
  }

  return Node::null();
}

TypeNode MyQuantifiersModule::findTypeByName(const std::string& name)
{
  for ( auto type_ : d_types )
  {
    if ( type_.hasName() && type_.getName() == name )
    {
      return type_;      
    }
    else if ( type_.isDatatype() && type_.getDType().getName() == name )
    {
      return type_;
    }
  }

  return TypeNode::null();
}

Node MyQuantifiersModule::findConstructorBySelector(Node sel, const DType& dt)
{
  const std::vector<std::shared_ptr<DTypeConstructor>>& constrs =
    dt.getConstructors();
  
  for ( size_t i = 0; i < constrs.size(); i++ )
  {
    std::shared_ptr<DTypeConstructor> constr = constrs[i];
  
    if ( constr->getSelectorIndexInternal(sel) >= 0 )
    {
      return constr->getConstructor();
    }
  }

  return Node::null();
}

Node MyQuantifiersModule::findConstructorByName(const std::string& name, const DType& dt)
{
  const std::vector<std::shared_ptr<DTypeConstructor>>& constrs =
    dt.getConstructors();
  
  for ( size_t i = 0; i < constrs.size(); i++ )
  {
    std::shared_ptr<DTypeConstructor> constr = constrs[i];
  
    if ( constr->getName() == name )
    {
      return constr->getConstructor();
    }
  }

  return Node::null();
}

void MyQuantifiersModule::eliminateDestructorsInLemmaCandidates()
{
  for ( size_t i = 0; i < d_lemma_cands.size(); i++ )
  {
    for ( size_t j = 0; j < d_lemma_cands[i].size(); j++ )
    {
      d_lemma_cands[i][j] = eliminateDestructors(d_lemma_cands[i][j]);
    }
  }

  return;
}

void MyQuantifiersModule::eliminateDestructorsInExample()
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();

  TypeNode nat = findTypeByName("Nat");
  Node deep_add = findOperatorByName("deep-add");
  Node succ = findOperatorByName("succ");
  Node pred = findOperatorByName("pred");
  Node m = sm->mkDummySkolem("m", nat);
  Node n = sm->mkDummySkolem("n", nat);

  Node e0 = nm->mkNode(Kind::APPLY_SELECTOR, pred, m);
  Node e1 = nm->mkNode(Kind::APPLY_UF, deep_add, e0, n);
  Node e2 = nm->mkNode(Kind::APPLY_CONSTRUCTOR, succ, e1);
  Node e3 = nm->mkNode(Kind::APPLY_UF, deep_add, m, n);
  Node example = nm->mkNode(Kind::EQUAL, e2, e3);

  std::cout << example << " ==> ";
  std::cout << example << std::endl;

  return;
}

void MyQuantifiersModule::filterRelevantInequationsBySampling()
{
  NodeManager* nm = NodeManager::currentNM();
  eq::EqualityEngine* ee = getEqualityEngine();

  std::vector<Node> flawed_goals;

  for ( auto goal : d_rel_ineqns ) 
  {
    if ( d_samples.find(goal) != d_samples.end() )
    {
      std::vector<Node> substn_dom = d_samples[goal].first;

      for ( size_t i = 0; i < 5; i++ )
      {
        std::vector<Node> substn_img = d_samples[goal].second[i];
        
        Node lhs = evaluate(goal[0], substn_dom, substn_img, true);
        Node rhs = evaluate(goal[1], substn_dom, substn_img, true);

        if ( !ee->hasTerm(lhs) || 
             !ee->hasTerm(rhs) || 
             !ee->areEqual(lhs, rhs) )
        {
          flawed_goals.push_back(goal);
        }
      }
    }
    else
    {
      std::vector<Node> substn_dom;
      collectSkolemVariablesInTerm(goal, substn_dom);
      d_samples[goal] = make_pair(substn_dom, 
        std::array<std::vector<Node>, 5>{});
      std::vector<std::vector<Node>> substn_imgs;
      generateSubstitutionImages(5, substn_dom, substn_imgs);
      for ( size_t i = 0; i < 5; i++ )
      {
        d_samples[goal].second[i] = substn_imgs[i];

        for ( size_t j = 0; j < 2; j++ )
        {
          Node t = evaluate(goal[j], substn_dom, substn_imgs[i], true);
          
          if ( !ee->hasTerm(t) )
          {
            d_qim.addPendingLemma(
              nm->mkNode(Kind::APPLY_UF, d_type_pred[t.getType()], t),
              InferenceId::QUANTIFIERS_CONJ_GEN_GT_ENUM);
          }
        }
      }
      flawed_goals.push_back(goal);
    }
  }

  std::vector<Node> prev_goals;
  prev_goals.insert(prev_goals.end(), d_rel_ineqns.begin(), d_rel_ineqns.end());

  d_rel_ineqns.clear();
  for ( auto goal : prev_goals )
  {
    if ( std::find(flawed_goals.begin(), flawed_goals.end(), goal) == 
           flawed_goals.end() )
    {
      d_rel_ineqns.push_back(goal);
    }
  }
}

void MyQuantifiersModule::filterExamplesBySampling()
{
  eq::EqualityEngine* ee = getEqualityEngine();

  if ( d_stashed )
  {
    std::vector<Node> substn_dom = d_sample_stash[0].first;

    for ( size_t i = 0; i < 5; i++ )
    {
      std::vector<Node> substn_rng = d_sample_stash[0].second[i];

      Node evaled_lhs = evaluate(d_lhs_stash, substn_dom, substn_rng, true);
      Node evaled_rhs = evaluate(d_rhs_stash, substn_dom, substn_rng, true);
      
      if ( ee->hasTerm(evaled_lhs) && ee->hasTerm(evaled_rhs) )
      {
        std::cout << "[sample #" << i << " " << 
          (ee->areEqual(evaled_lhs, evaled_rhs) ? "success" : "failure") << 
          "]" << std::endl;
      }
      else
      {
        std::cout << "[skipped sample #" << i << "]" << std::endl;
      }
    }
  }
  else
  {
    NodeManager* nm = NodeManager::currentNM();
  
    TypeNode nat = findTypeByName("Nat");
    Node zero = findConstructorByName("zero", nat.getDType());
    Node succ = findConstructorByName("succ", nat.getDType());
    Node deep_add = findOperatorByName("deep-add");
    Node m = d_termCanon.getCanonicalFreeVar(nat, 0);
    Node n = d_termCanon.getCanonicalFreeVar(nat, 1);

    d_lhs_stash = nm->mkNode(Kind::APPLY_CONSTRUCTOR, succ, nm->mkNode(Kind::APPLY_UF, deep_add, m, n));
    d_rhs_stash = nm->mkNode(Kind::APPLY_UF, deep_add, nm->mkNode(Kind::APPLY_CONSTRUCTOR, succ, m), n);

    Node zero_ = nm->mkNode(Kind::APPLY_CONSTRUCTOR, zero);
    Node one = nm->mkNode(Kind::APPLY_CONSTRUCTOR, succ, zero_);
    Node two = nm->mkNode(Kind::APPLY_CONSTRUCTOR, succ, one);
    Node three = nm->mkNode(Kind::APPLY_CONSTRUCTOR, succ, two);
    Node four = nm->mkNode(Kind::APPLY_CONSTRUCTOR, succ, three);

    d_sample_stash.push_back(
      std::make_pair(
        std::vector<Node>{ m, n },
        std::array<std::vector<Node>, 5>{}));
    d_sample_stash[0].second[0] = std::vector<Node>{ zero_, zero_ };
    d_sample_stash[0].second[1] = std::vector<Node>{ one, zero_ };
    d_sample_stash[0].second[2] = std::vector<Node>{ two, zero_ };
    d_sample_stash[0].second[3] = std::vector<Node>{ three, zero_ };
    d_sample_stash[0].second[4] = std::vector<Node>{ four, zero_ };    

    for ( auto term : std::vector<Node>{ d_lhs_stash, d_rhs_stash } )
    {
      for ( auto substn_rng : d_sample_stash[0].second )
      {
        Node evaled_term = evaluate(term, d_sample_stash[0].first, substn_rng, true);
  
        if ( !ee->hasTerm(evaled_term) )
        {
          d_qim.addPendingLemma(
            nm->mkNode(
              Kind::APPLY_UF, 
              d_type_pred[evaled_term.getType()],
              evaled_term),
            InferenceId::QUANTIFIERS_CONJ_GEN_GT_ENUM);
        }
      } 
    }

    d_stashed = true;
  }

  // eq::EqualityEngine* ee = getEqualityEngine();
  // NodeManager* nm = NodeManager::currentNM();

  // TypeNode nat = findTypeByName("Nat");
  // Node zero = findConstructorByName("zero", nat.getDType());
  // Node succ = findConstructorByName("succ", nat.getDType());
  // Node deep_add = findOperatorByName("deep-add");
  // Node m = d_termCanon.getCanonicalFreeVar(nat, 0);
  // Node n = d_termCanon.getCanonicalFreeVar(nat, 1);
  // Node one = nm->mkNode(Kind::APPLY_CONSTRUCTOR, succ, nm->mkNode(Kind::APPLY_CONSTRUCTOR, zero));
  // Node two = nm->mkNode(Kind::APPLY_CONSTRUCTOR, succ, one);
  // Node lhs = nm->mkNode(Kind::APPLY_CONSTRUCTOR, succ, nm->mkNode(Kind::APPLY_UF, deep_add, two, two));
  // Node rhs = nm->mkNode(Kind::APPLY_UF, deep_add, nm->mkNode(Kind::APPLY_CONSTRUCTOR, succ, two), two);
  // Node lhs_lemma = nm->mkNode(Kind::APPLY_UF, d_type_pred[nat], lhs);
  // Node rhs_lemma = nm->mkNode(Kind::APPLY_UF, d_type_pred[nat], rhs);

  // d_qim.addPendingLemma(rhs_lemma, InferenceId::QUANTIFIERS_CONJ_GEN_GT_ENUM);
  // d_qim.addPendingLemma(lhs_lemma, InferenceId::QUANTIFIERS_CONJ_GEN_GT_ENUM);
  // if ( ee->hasTerm(lhs) && ee->hasTerm(rhs) )
  // {
  //   std::cout << "[" << (ee->areEqual(lhs, rhs) ? "success" : "failure") <<
  //     "]" << std::endl;
  // }
  // else
  // {
  //   std::cout << "[skip]" << std::endl;
  // }

  // if ( ee->hasTerm(lhs) )
  // {
  //   if ( ee->hasTerm(rhs) )
  //   {
  //     // std::cout << "lhs22 = " << lhs22 << std::endl;
  //     // std::cout << "rhs22 = " << rhs22 << std::endl;
  //     // std::cout << "lhs22 and rhs22 are " << 
  //     //   (ee->areEqual(lhs22, rhs22) ? "equal" : "not equal") << std::endl;
  //   }
  //   else
  //   {
      
  //     std::cout << "added rhs to equality engine" << std::endl;
  //   }
  // }
  // else
  // {

  //   std::cout << "added lhs to equality engine" << std::endl;
  // }

  // for ( auto term : std::vector<Node>{ lhs00, lhs02, lhs20, lhs22, 
  //                                      rhs00, rhs02, rhs20, rhs22 } )
  // {
  //   if ( !ee->hasTerm(term) )
  //   {
  //     d_qim.addPendingLemma(
  //       nm->mkNode(Kind::APPLY_UF, d_type_pred[term.getType()], term),
  //       InferenceId::QUANTIFIERS_CONJ_GEN_GT_ENUM);

  //     std::cout << "[added lemma for " << term << "]" << std::endl;
  //   }
  // }

  // std::cout << "lhs00 == rhs00 ?" << ee->areEqual(lhs00, rhs00) << std::endl;
  // std::cout << "lhs02 == rhs02 ?" << ee->areEqual(lhs02, rhs02) << std::endl;
  // std::cout << "lhs20 == rhs20 ?" << ee->areEqual(lhs20, rhs20) << std::endl;
  // std::cout << "lhs22 == rhs22 ?" << ee->areEqual(lhs22, rhs22) << std::endl;

  // eq::EqualityEngine* ee = getEqualityEngine();
  // NodeManager* nm = NodeManager::currentNM();
  // SkolemManager* sm = nm->getSkolemManager();
  // SygusSampler ss{ d_env };

  // TypeNode nat = findTypeByName("Nat");
  // Node zero = findConstructorByName("zero", nat.getDType());
  // Node succ = findConstructorByName("succ", nat.getDType());
  // Node deep_add = findOperatorByName("deep-add");
  // Node m = d_termCanon.getCanonicalFreeVar(nat, 0);
  // Node n = d_termCanon.getCanonicalFreeVar(nat, 1);

  // // succ(deep-add(m, n)) = deep-add(succ(m), n)
  // Node e0 = nm->mkNode(Kind::APPLY_UF, deep_add, m, n);
  // Node lhs = nm->mkNode(Kind::APPLY_CONSTRUCTOR, succ, e0);
  // Node e2 = nm->mkNode(Kind::APPLY_CONSTRUCTOR, succ, m);
  // Node rhs = nm->mkNode(Kind::APPLY_UF, deep_add, e2, n);

  // ss.initialize(nat, std::vector<Node>{m, n}, 2);
  // std::cout << "ss.registerTerm(" << lhs << ") = " << 
  //   ss.registerTerm(lhs, true) << std::endl;
  // std::cout << "ss.registerTerm(" << rhs << ") = " << 
  //   ss.registerTerm(rhs) << std::endl;

  // for ( size_t i = 0; i < 2; i++ )
  // {
  //   for ( auto evaled_term : 
  //           std::vector<Node>{ ss.evaluate(lhs, i), ss.evaluate(rhs, i) } )
  //   {
  //     if ( !ee->hasTerm(evaled_term) )
  //     {
  //       Node pred = d_type_pred[evaled_term.getType()];
  //       Node lemma = nm->mkNode(Kind::APPLY_UF, pred, evaled_term);
  //       d_qim.addPendingLemma(lemma, InferenceId::QUANTIFIERS_CONJ_GEN_GT_ENUM);
  //     }
  //   }
  // }

  // // int i = ss.getDiffSamplePointIndex(lhs, rhs);
  // // if ( i >= 0 )
  // // {
  // //   std::vector<Node> pt = ss.getSamplePoint(i);
  // //   std::cout << "{";
  // //   { 
  // //     bool fst = true;
  // //     for ( auto coord : pt )
  // //     {
  // //       if ( fst )
  // //       {
  // //         fst = false;
  // //       }
  // //       else
  // //       {
  // //         std::cout << ", ";
  // //       }
  // //       std::cout << coord;
  // //     }
  // //   }
  // //   std::cout << "}" << std::endl;
  // // }
  // // else
  // // {
  // //   std::cout << "they aren't different at the sample points" << std::endl;
  // // }
  // // std::cout << "they differ at sample point #" << i << std::endl;

  return;
}

void MyQuantifiersModule::populateDummyPredicates()
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  
  for ( auto type_ : d_types )
  {
    if ( d_type_pred.find(type_) == d_type_pred.end() )
    {
      TypeNode type_pred_type = nm->mkFunctionType(type_, nm->booleanType());
      d_type_pred[type_] = sm->mkDummySkolem("P", type_pred_type);
    }
  }
  return;
}

void MyQuantifiersModule::generalizeLemmaCandidates()
{
  std::vector<Node> goals;
  goals.insert(goals.end(), d_rel_ineqns.begin(), d_rel_ineqns.end());

  d_rel_ineqns.clear();

  for ( size_t i = 0; i < goals.size(); i++ )
  {
    Node goal = goals[i];
    d_rel_ineqns.push_back(
      d_termCanon.getCanonicalTerm(generalizeTerm(goal), true));

    std::vector<Node> prev_cands;
    prev_cands.insert(prev_cands.end(), d_lemma_cands[i].begin(), d_lemma_cands[i].end());

    d_lemma_cands[i].clear();

    for ( auto cand_ : prev_cands )
    {
      Node cand = generalizeTerm(cand_);
      Node canon_cand = d_termCanon.getCanonicalTerm(cand, true);

      if ( (canon_cand != d_rel_ineqns[i]) &&
           (std::find(d_lemma_cands[i].begin(), d_lemma_cands[i].end(), 
                      canon_cand) == d_lemma_cands[i].end()) )
      {
        d_lemma_cands[i].push_back(cand);
      }
    }

    prev_cands.clear();
  }

  goals.clear();

  return;
}

void MyQuantifiersModule::generalizeExample()
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();  

  TypeNode nat_ = findTypeByName("Nat");
  Node succ_ = findConstructorByName("succ", nat_.getDType());
  Node add_ = findOperatorByName("add");
  Node deep_add_ = findOperatorByName("deep-add");
  Node m_ = sm->mkDummySkolem("m", nat_, "",
    SkolemManager::SkolemFlags::SKOLEM_EXACT_NAME);
  Node n_ = sm->mkDummySkolem("n", nat_, "",
    SkolemManager::SkolemFlags::SKOLEM_EXACT_NAME);

  // std::cout << "Output of generalization is " << 
  //  generalizeAndCanonize(nm->mkNode(Kind::EQUAL, terms[0], terms[1])) << 
  //  std::endl;
}

Node MyQuantifiersModule::generalizeTerm(Node root_term)
{
  std::set<Node> subterms[2];
  for ( size_t i = 0; i < 2; i++ )
  {
    NodeDfsIterable iter(root_term[i], VisitOrder::PREORDER,
      std::function<bool(TNode)>([](TNode n)
      {
        return n.isVar();
      }));

    NodeDfsIterator limit = iter.end();

    for ( NodeDfsIterator cursor = iter.begin();
          cursor != limit;
          cursor++ )
    {
      subterms[i].insert(*cursor);
    }
  }

  std::set<Node> shared;
  std::set_intersection(
    subterms[0].begin(), subterms[0].end(), 
    subterms[1].begin(), subterms[1].end(), 
    std::inserter<std::set<Node>>(shared, shared.begin()));

  // Type definitions

  enum Cmd { EXAMINE, CONSTRUCT };

  struct Job { Cmd c; Node t; Kind k; size_t arity; };

  // State variables

  NodeManager* nm = NodeManager::currentNM();
  
  std::map<Node, Node> substn;

  std::vector<struct Job> wrklst;
  wrklst.push_back(Job{EXAMINE, root_term, Kind::NULL_EXPR, 0});

  std::vector<Node> stk;

  size_t counter = 0;

  // Algorithm

  while ( !wrklst.empty() )
  {
    Job curr_job = wrklst.back();
    wrklst.pop_back();

    Cmd cmd = curr_job.c;
    Node term = curr_job.t;

    if ( cmd == EXAMINE && 
         term.isConst() && 
         (shared.find(term) != shared.end()) )
    {
      shared.erase(term);
      substn[term] = 
        nm->mkBoundVar("x" + std::to_string(counter),
                       term.getType());
      counter++;
      stk.push_back(substn[term]);
    }
    else if ( cmd == EXAMINE && 
              term.isConst() )
    {
      stk.push_back(term);
    }
    else if ( cmd == EXAMINE && 
              term.isVar() && 
              (substn.find(term) != substn.end()) )
    {
      stk.push_back(substn[term]);
    }
    else if ( cmd == EXAMINE && 
              term.isVar() )
    {
      substn[term] = 
        nm->mkBoundVar("x" + std::to_string(counter),
                       term.getType());
      counter++;
      stk.push_back(substn[term]);
    }
    else if ( cmd == EXAMINE &&
              term.hasOperator() &&
              (shared.find(term) != shared.end()) )
    {
      shared.erase(term);
      substn[term] = 
        nm->mkBoundVar("x" + std::to_string(counter),
                       term.getType());
      counter++;
      stk.push_back(substn[term]);
    }
    else if ( cmd == EXAMINE &&
              term.hasOperator() &&
              (substn.find(term) != substn.end()) )
    {
      stk.push_back(substn[term]);
    }
    else if ( cmd == EXAMINE && 
              term.hasOperator() )
    {
      wrklst.push_back(
        Job{CONSTRUCT, term.getOperator(), term.getKind(), 
            term.getNumChildren()});

      for ( auto child : term )
      {
        wrklst.push_back(Job{EXAMINE, child, Kind::NULL_EXPR, 0});
      }
    }
    else
    {
      Assert( cmd == CONSTRUCT );

      std::vector<Node> children;

      if ( term.getKind() != Kind::BUILTIN )
      {
        children.push_back(term);
      }

      for ( size_t i = 0; i < curr_job.arity; i++ ) 
      {
        children.push_back(stk.back());
        stk.pop_back();
      }

      stk.push_back(nm->mkNode(curr_job.k, children));
    }
  }

  return stk.back();
}

void MyQuantifiersModule::bindVarsInLemmas()
{
  for ( size_t i = 0; i < d_lemma_cands.size(); i++ )
  {
    for ( size_t j = 0; j < d_lemma_cands[i].size(); j++ )
    {
      Node lemma = d_lemma_cands[i][j];
   
      std::vector<Node> bvs;

      NodeDfsIterable iter(lemma);
      NodeDfsIterator limit = iter.end();
      for ( NodeDfsIterator cursor = iter.begin();
            cursor != limit;
            cursor++ )
        {
          if ((*cursor).isVar())
          { 
            bvs.push_back(*cursor);
          }
        }      
            
      NodeManager* nm = NodeManager::currentNM();
      d_lemma_cands[i][j] = 
        nm->mkNode(Kind::FORALL, nm->mkNode(Kind::BOUND_VAR_LIST, bvs), lemma);
    }
  }
}

void MyQuantifiersModule::promptForLemma()
{
  std::cout << std::endl << "Pick a lemma: ";

  char yesOrNo = getchar();

  if ( yesOrNo == 'Y' )
  {
    std::string choice_strs[2] = { "", "" };
    char ch = 0;

    for ( size_t i = 0; i < 2; i++ )
    {
      ch = getchar();

      while ( ch != (i == 0 ? '.' : '\n') )
      {
        choice_strs[i].push_back(ch);
        
        ch = getchar();
      } 
    }

    size_t choices[2];
    for ( size_t i = 0; i < 2; i++ )
    {
      choices[i] = stoi(choice_strs[i]);
    }

    if ( choices[0] < d_rel_ineqns.size() &&
         choices[1] < d_lemma_cands[choices[0]].size() )
    {
      Node subgoal = d_lemma_cands[choices[0]][choices[1]];

      NodeManager* nm = NodeManager::currentNM();

      d_qim.addPendingLemma(
        nm->mkNode(Kind::OR, subgoal.negate(), subgoal),
        InferenceId::QUANTIFIERS_CONJ_GEN_SPLIT);
      
      d_qim.addPendingPhaseRequirement(subgoal, false);

      d_qim.doPendingLemmas();

      d_qim.doPendingPhaseRequirements();
    }
    else
    {
      std::cout << "<<skip>>" << std::endl;
    }
  }
  else
  {
    getchar();

    std::cout << "<<skip>>" << std::endl;
  }

  // for ( size_t i = 0; i < d_rel_ineqns.size(); i++ )
  // {
  //   if ( !d_lemma_cands[i].empty() )
  //   {
  //     for ( auto lemma : d_lemma_cands[i] )
  //     {
  //       NodeManager* nm = NodeManager::currentNM();
     
  //       d_qim.addPendingLemma(
  //         nm->mkNode(Kind::OR, lemma.negate(), lemma),
  //         InferenceId::QUANTIFIERS_CONJ_GEN_SPLIT);
      
  //       d_qim.addPendingPhaseRequirement(lemma, false);
  //     }

  //     break;
  //   }
  // }
}

void MyQuantifiersModule::printGroundTermsEquivalentToSubterms() 
{
  // In this function, we want to see if there is information in the environment
  // that turns seemingly unprovable lemma candidates provable.
  // I should probably explain this better.
  // Consider the usual definitions of '+' and '*' on the usual natural number
  // datatype.
  // It's definitely a bad choice to try to prove a lemma candidate based on
  // the following goal:
  //     sk0 * sk1 = sk0 * sk2 + sk0 * sk1
  // But what if we know sk2 was equivalent to the concrete term 0?
  // We'd then try to prove a lemma candidate based on the following goal:
  //     sk0 * sk1 = sk0 * 0 + sk0 * sk1
  // That would certainly make more sense!
  // 
  // However I need to see how much each lemma candidate can be simplified
  // using contextual information.
  // I intend to do this by printing out both the representative and the ground
  // term corresponding to each subterm of a lemma candidate before destructor
  // elimination, and definitely before quantifiers are introduced.
  //
  // The plan is to take a '<GOAL NUMBER>.<LEMMA NUMBER>' or 'X' (for stop)
  // command from the user.
  // In the former case if we're given G.L we'll print the representative and
  // the concrete term for each subterm of the lemma candidate L for goal G.
  // If there is no goal G or no lemma L, we should complain and ask again.
  // Once it's printed we'll make another request from the user.
  // In the latter case we just don't ask the user for any further input.
  // If the input is illegal, we should just ask again.

  bool halt = false;
  bool parsed = false;
  std::string command = "";
  std::string post_period = "";
  size_t period_index = 0;
  size_t goal_number = 0;
  size_t lemma_number = 0;

  while ( !halt ) 
  {
    std::cout << "> ";
    std::getline(std::cin, command);

    if ( command.compare("X") == 0 ) 
    {
      halt = true;
    }
    else
    {
      try
      {
        goal_number = std::stoi(command, &period_index);
        post_period = command.substr(period_index + 1);
        lemma_number = std::stoi(post_period, &period_index);
        parsed = (period_index == post_period.size());
      }
      catch ( const std::invalid_argument& e )
      {
        parsed = false;
      }
      catch ( const std::out_of_range& e )
      {
        parsed = false;
      } 

      if ( parsed )
      {
        if ( goal_number < d_lemma_cands.size() && 
             lemma_number < d_lemma_cands[goal_number].size() )
        {
          // 'selected lemma'
          Node sel_lem = d_lemma_cands[goal_number][lemma_number];

          std::cout << "{";

          bool first = true;

          // 'selected lemma buffer'
          NodeDfsIterable sel_lem_buf(sel_lem);
          // 'point max'
          NodeDfsIterator pt_max = sel_lem_buf.end();
          // 'point'
          for ( NodeDfsIterator pt = sel_lem_buf.begin();
                pt != pt_max; pt++ )
          { 
            if ( first ) 
            {
              first = false;
            }
            else
            {
              std::cout << ", ";
            }

            std::cout << "(";

            // 'term at point'
            Node term = *pt;
            std::cout << term << ",";
            // 'representative of term'
            Node repr = d_qstate.getRepresentative(term);
            std::cout << repr << ",";
            // '(reference for) concrete term equivalent to repr'
            std::map<Node,Node>::iterator concrete = d_ground_eqc_map.find(repr);
            if ( concrete != d_ground_eqc_map.end() )
            {
              std::cout << *concrete;
            }
            else
            {   
              std::cout << "-";
            }
            
            std::cout << ")";
          }

          std::cout << "}" << std::endl;
        }
        else
        {
          std::cout << "<<no G.L>>" << std::endl;
        }
      }
      else 
      {
        std::cout << "<<no parse>>" << std::endl;
      }
    }
  }
}

Node MyQuantifiersModule::concretizeTerm(Node in_term)
{
  // in_term is 'input term'

  enum Command { examine, construct };
  struct Job { Command cmd; Node term; Kind kind; size_t arity; };

  std::vector<Job> jobs;
  std::vector<Node> results;  

  jobs.push_back({ examine, in_term, Kind::NULL_EXPR, 0 });

  while ( !jobs.empty() )
  {
    // display the job stack ======
    // {
    //   std::cout << "**job stack** ";
    //   bool first = true;
    //   for ( auto j : jobs )
    //   {
    //     if ( first ) { first = false; } else { std::cout << "; "; }
    // 
    //     switch ( j.cmd ) 
    //     { 
    //       case examine: 
    //       { 
    //         std::cout << "examine(" << j.term << ")"; 
    //         break; 
    //       } 
    // 
    //       case construct: 
    //       { 
    //         std::cout << "construct(" << j.kind << "," << j.arity << ")";
    //         break; 
    //       }
    //     }
    //   }
    //   std::cout << std::endl;
    // }
    // ============================

    // display the result stack ==========
    // {
    //   std::cout << "**result stack** ";
    //   bool first = true;
    //   for ( auto res : results )
    //   {
    //     if ( first ) { first = false; } else { std::cout << "; "; }
    //     std::cout << res;
    //   }
    //   std::cout << std::endl;
    // }
    // ===================================

    Job cj = jobs.back(); // cj is 'current job'
    jobs.pop_back();

    switch ( cj.cmd )
    {
      case examine:
      {
        Node cterm = cj.term; // 'current term'

        Node repr = d_qstate.getRepresentative(cterm); // 'representative'

        std::map<Node,Node>::iterator concr; // 'concrete'
        concr = d_ground_eqc_map.find(repr);

        if ( concr != d_ground_eqc_map.end() )
        {
          results.push_back(concr->second);
        }

        else if ( cterm.hasOperator() )
        {
          Node op = cterm.getOperator();
          bool builtin = (op.getKind() == Kind::BUILTIN);

          // std::cout << "!!" << op << ".getKind() == " << op.getKind() << "!! ";
          // std::cout << "!!" << "builtin: " << builtin << "!!" << std::endl;

          size_t extra_childs = 0; // 'extra children'
  
          if ( !builtin )
          {
            extra_childs = 1;
            results.push_back( op );
          }

          jobs.push_back({ construct, 
                           Node::null(), 
                           cterm.getKind(),
                           cterm.getNumChildren() + extra_childs });

          for ( auto ri = cterm.rbegin(); ri != cterm.rend(); ri++ )
          {
            jobs.push_back({ examine, *ri, Kind::NULL_EXPR, 0 });
          }
        }

        else
        {
          results.push_back(cterm);
        }
        
        break;
      }

      case construct:
      {
        std::vector<Node> childs; // 'children'

        Assert( results.size() >= cj.arity );        

        childs.insert( childs.begin(), results.end() - cj.arity, results.end() );

        // size_t ct = 0; // 'count'
        // 
        // std::vector<Node>::reverse_iterator ri;  // 'reverse iterator'
        // ri = results.rbegin();
        // 
        // while ( ct < cj.arity )
        // {
        //   childs.push_back(*ri);
        //   ri++;
        //   ct++;
        // }
      
        for ( size_t i = 0; i < cj.arity; i++ )
        {
          results.pop_back();
        }

        // print childs ==========
        // { 
        //   std::cout << "**childs** ";
        //   bool first = true;        
        //   for ( auto child : childs )
        //   {
        //     if ( first ) { first = false; } else { std::cout << ", "; }
        //     std::cout << child;
        //   } 
        //   std::cout << std::endl;
        // }
        // =======================

        results.push_back(
          NodeManager::currentNM()->mkNode(cj.kind, childs));

        break;
      }
    }
  }

  Node ans = results.back(); // ans is 'answer'
  results.pop_back();

  return ans;
}

void MyQuantifiersModule::showConcreteLemmaCandidates()
{
  size_t gidx = 0; // 'goal index'
  size_t lidx = 0; // 'lemma index'

  for ( auto cands : d_lemma_cands  )
  {
    lidx = 0;

    for ( auto cand : cands )
    {
      std::cout << gidx << "." << lidx << ". " << concretizeTerm(cand) << std::endl;

      lidx++;
    }

    gidx++;
  }

  // if ( d_lemma_cands.size() > 0 && d_lemma_cands[0].size() > 0 )
  // {
  //   std::cout << "0.0. " << concretizeTerm(d_lemma_cands[0][0]) << std::endl;
  // }
  // else
  // {
  //   std::cout << "<<no lemmas to concretize>>" << std::endl;
  // }
}

} // namespace quantifiers
} // namespace theory
} // namespace cvc5::internal
