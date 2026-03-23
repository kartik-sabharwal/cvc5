#include "preprocessing/passes/cone_of_influence.h"

#include "expr/node_algorithm.h"
#include "preprocessing/assertion_pipeline.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

ConeOfInfluence::ConeOfInfluence(PreprocessingPassContext* ppc)
    : PreprocessingPass(ppc, "cone-of-influence")
{
}

PreprocessingPassResult ConeOfInfluence::applyInternal(AssertionPipeline* ap)
{
  Trace("cone-of-influence") << "Initializing...";

  const size_t num_asserts = ap->size();

  const Node tt = nodeManager()->mkConst(true);

  std::vector<std::vector<TNode>> syms_in_assert;
  syms_in_assert.resize(num_asserts);

  std::unordered_map<TNode, std::vector<size_t>> asserts_with;

  std::vector<size_t> itinerary;

  std::unordered_set<size_t> visited;

  Trace("cone-of-influence") << "done." << std::endl;

  Trace("cone-of-influence") << "Constructing syms_in_assert and asserts_with..." << std::endl;

  for (size_t i = 0; i < num_asserts; ++i)
  {
    std::unordered_set<Node> syms;
    TNode phi = ap->operator[](i);

    Trace("cone-of-influence") << "Getting syms_in_assert[" << i << "]..." << std::endl;

    std::vector<TNode>& syms_in_this_assert = syms_in_assert[i];

    Trace("cone-of-influence") << "..got it." << std::endl;

    Trace("cone-of-influence") << "Processing assertion " << phi << " {" << std::endl;

    Trace("cone-of-influence") << "Getting variables in assertion..." << std::endl;

    expr::getSubtermsKind(Kind::VARIABLE, phi, syms, false);

    Trace("cone-of-influence") << "...got." << std::endl;

    for (TNode sym : syms)
    {
      Trace("cone-of-influence") << "Adding to syms_in_this_assert..." << std::endl;

      syms_in_this_assert.push_back(sym);

      Trace("cone-of-influence") << "...added." << std::endl;

      Trace("cone-of-influence") << "Adding to asserts_with..." << std::endl;

      asserts_with[sym].push_back(i);

      Trace("cone-of-influence") << "...added." << std::endl;
    }

    Trace("cone-of-influence") << "Adding goals to itinerary..." << std::endl;

    if (phi.getKind() == Kind::NOT)
    {
      itinerary.push_back(i);
    }

    Trace("cone-of-influence") << "...added." << std::endl;

    Trace("cone-of-influence") << "}" << std::endl;
  }

  Trace("cone-of-influence") << "...done." << std::endl;

  if (TraceIsOn("cone-of-influence"))
  {
    std::ostream& out = Trace("cone-of-influence");

    out << "syms in assert {" << std::endl;
    for (size_t i = 0; i < num_asserts; ++i)
    {
      out << "assertion #" << i << " maps to " << syms_in_assert[i]
          << std::endl;
    }
    out << "}" << std::endl;

    out << "asserts_with {" << std::endl;
    for (std::pair<TNode, std::vector<size_t>> entry : asserts_with)
    {
      out << std::get<0>(entry) << " maps to";
      for (const size_t i : std::get<1>(entry))
      {
        out << " " << i;
      }
      out << std::endl;
    }
    out << "}" << std::endl;

    out << "goals {" << std::endl;
    for (const size_t i : itinerary)
    {
      out << ap->operator[](i) << std::endl;
    }
    out << "}" << std::endl;
  }

  Trace("cone-of-influence") << "Running the DFS..." << std::endl;

  while (!itinerary.empty())
  {
    const size_t dest = itinerary.back();
    itinerary.pop_back();

    if (member(visited, dest))
    {
      continue;
    }
    else
    {
      visited.insert(dest);
      
      std::vector<TNode>& syms_in_dest = syms_in_assert[dest];

      for (TNode sym : syms_in_dest)
      {
        std::vector<size_t>& asserts_with_sym = asserts_with[sym];
        itinerary.insert(
            itinerary.end(), asserts_with_sym.begin(), asserts_with_sym.end());
      }
    }
  }

  Trace("cone-of-influence") << "...done." << std::endl;

  Trace("cone-of-influence") << "Discard assertions {" << std::endl;
  for (size_t i = 0; i < num_asserts; ++i)
  {
    if (member(visited, i))
    {
      continue;
    }
    else
    {
      Trace("cone-of-influence") << ap->operator[](i) << std::endl;

      ap->replace(i, tt);
      ap->ensureRewritten(i);
    }
  }
  Trace("cone-of-influence") << "}" << std::endl;

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
