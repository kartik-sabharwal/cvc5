/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Apply substitutions preprocessing pass.
 *
 * Apply top level substitutions to assertions, rewrite, and store back into
 * assertions.
 */

#include "preprocessing/passes/apply_substs.h"

#include "context/cdo.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/env.h"
#include "theory/substitutions.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "util/string.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

ApplySubsts::ApplySubsts(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "apply-substs")
{
}

PreprocessingPassResult ApplySubsts::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  verbose(2) << "applying substitutions..." << std::endl;
  Trace("apply-substs") << "ApplySubsts::processAssertions(): "
                        << "applying substitutions" << std::endl;
  // TODO(#1255): Substitutions in incremental mode should be managed with a
  // proper data structure.

  theory::TrustSubstitutionMap& tlsm =
      d_preprocContext->getTopLevelSubstitutions();
  unsigned size = assertionsToPreprocess->size();
  for (unsigned i = 0; i < size; ++i)
  {
    if (assertionsToPreprocess->isSubstsIndex(i))
    {
      continue;
    }

    // Kartik.  If the formula is universally quantified and has the ID
    // 'definition' we preserve it.
    const Node& phi = (*assertionsToPreprocess)[i];

    // Only delve deeper if the formula is annotated.
    if (phi.getNumChildren() == 3)
    {
      const Node& anns = phi[2];

      // Find the first child of the annotations node that has the
      // kind INST_ATTRIBUTE and whose own first child has the kind
      // CONST_STRING and the value "qid".
      for (size_t ann_idx = 0; ann_idx < anns.getNumChildren(); ann_idx++)
      {
        const Node& ann = anns[ann_idx];
        
        if (ann.getKind() == Kind::INST_ATTRIBUTE)
        {
          const Node& key_node = ann[0];
          
          if (key_node.getKind() == Kind::CONST_STRING)
          {
            const std::string& key_str = key_node.getConst<String>().toString();

            if (key_str == "qid" && ann[1].getName() == "definition")
            {
              d_env.preserveFormula(phi);
            }
          }
        }
      }
    }
    // * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
    
    Trace("apply-substs") << "applying to " << (*assertionsToPreprocess)[i]
                          << std::endl;
    d_preprocContext->spendResource(Resource::PreprocessStep);
    assertionsToPreprocess->replaceTrusted(
        i,
        tlsm.applyTrusted((*assertionsToPreprocess)[i], d_env.getRewriter()));
    Trace("apply-substs") << "  got " << (*assertionsToPreprocess)[i]
                          << std::endl;
    // if rewritten to false, we are done
    if (assertionsToPreprocess->isInConflict())
    {
      return PreprocessingPassResult::CONFLICT;
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
