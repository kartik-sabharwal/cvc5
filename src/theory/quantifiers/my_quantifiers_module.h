#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__MY_QUANTIFIERS_MODULE_H
#define CVC5__THEORY__QUANTIFIERS__MY_QUANTIFIERS_MODULE_H

#include "expr/dtype_cons.h"
#include "expr/term_canonize.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class MyOpArgIndex 
{
 public:
  std::map<Node, MyOpArgIndex> d_children;
  std::vector<Node> d_ops;
  std::vector<Node> d_op_terms;
};

class MyQuantifiersModule : public QuantifiersModule 
{
 public:
  MyQuantifiersModule(Env& env, QuantifiersState& qs,
    QuantifiersInferenceManager& qim, QuantifiersRegistry& qr,
    TermRegistry& tr);

  ~MyQuantifiersModule();

  bool needsCheck(Theory::Effort e) override;

  void reset_round(Theory::Effort e) override;

  void check(Theory::Effort e, QEffort quant_e) override;

  std::string identify() const override;

  void clearFields();

  void collectEquivalenceClasses();

  void showEquivalenceClasses();

  void addTerm(MyOpArgIndex& root_op_arg_index, std::vector<Node> args, Node term);

  void buildOperatorArgumentIndices();

  bool isHandledTerm(Node n);

  void showOpArgIndices();

  void mapEquivalenceClassesToGroundTerms();

  Node getGroundTerm(MyOpArgIndex& root_op_arg_index);

  void showGroundTermsForEquivalenceClasses();

  void partitionEquivalenceClasses();

  void showFalsifiedEqualities();
  
  void showAssertedForalls();

  void showCurrentAssumptions();

  void collectRelevantInequations();

  void showRelevantInequations();

  void showLemmaCandidates();

  // void filterRelevantInequationsByExample();

  void collectSkolemVariablesInTerm(Node term, std::vector<Node>& sk_vars);

  void collectLemmaCandidates();

  void generateSubstitutionImages(
    size_t limit, std::vector<Node>& sk_vars,
    std::vector<std::vector<Node>>& substn_imgs);

  Node eliminateDestructors(Node term);

  void eliminateDestructorsInLemmaCandidates();

  void populateTypes();

  void populateDummyPredicates();

  void showTypes();

  Node findOperatorByName(const std::string& name);

  TypeNode findTypeByName(const std::string& name);

  std::pair<Node, Node> findDestructorApplication(Node term,
    std::map<TypeNode, size_t>& next_var);

  Node findConstructorBySelector(Node sel, const DType& dt);

  Node findConstructorByName(const std::string& name, const DType& dt);

  void eliminateDestructorsInExample();

  void filterRelevantInequationsBySampling();

  void filterExamplesBySampling();

  void generalizeLemmaCandidates();

  void generalizeExample();

  Node generalizeTerm(Node root_term);

  void bindVarsInLemmas();

  void promptForLemma();

  void printGroundTermsEquivalentToSubterms();

  Node concretizeTerm(Node in_term);

  void concretizeLemmaCandidates();

  Node replaceSkVarsWithBoundVars(Node orig);

  void replaceSkVarsWithBoundVarsInCands();

  // @Kartik.  All equivalence classes in the current model.
  std::vector<Node> d_eqcs;

  // @Kartik.  Equivalence classes that contain a skolem variable of datatype
  // sort.
  std::vector<Node> d_rel_eqcs;

  // @Kartik.  Equivalence classes that are not in d_rel_eqcs.
  std::vector<Node> d_irrel_eqcs;

  // @Kartik.  Map from equivalence class representatives to ground *values*
  // (ground terms that do not contain skolems).
  std::map<Node, Node> d_ground_eqc_map;

  std::map<Node, MyOpArgIndex> d_op_arg_indices;

  // @Kartik. 'Relevant inequation' is one attempt to describe a goal.
  // A relevant inequation (in to the current model) is an equality term
  // (the Kind of this Node is EQUAL) where at least one side is a member of a
  // 'relevant' equivalence class.
  std::vector<Node> d_rel_ineqns;

  // @Kartik.  I intend the i-th element of this vector to be the list of lemma
  // candidates associated with the i-th relevant inequation.
  std::vector<std::vector<Node>> d_lemma_cands;

  std::vector<TypeNode> d_types;

  expr::TermCanonize d_termCanon;

  std::map<TypeNode, Node> d_type_pred;

  std::vector<std::pair<std::vector<Node>, std::array<std::vector<Node>, 5>>> d_sample_stash;
  Node d_lhs_stash;
  Node d_rhs_stash;
  bool d_stashed;

  std::map<Node, 
           std::pair<std::vector<Node>, 
                     std::array<std::vector<Node>, 5>>> d_samples;
};

} // namespace quantifiers
} // namespace theory
} // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__MY_QUANTIFIERS_MODULE_H */
