/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The Z3AssertionPreparation preprocessing pass.
 */

#include "preprocessing/passes/z3_assertion_preparation.h"

#include "options/z3_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "z3/z3_quantifiers_engine.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

Z3AssertionPreparation::Z3AssertionPreparation(
    PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "z3-prep")
{
  if (options().z3.z3)
  {
    TheoryEngine* te = d_preprocContext->getTheoryEngine();
    z3::Z3QuantifiersEngine::get(te)->resetCore(te);
  }
}

PreprocessingPassResult Z3AssertionPreparation::applyInternal(
    AssertionPipeline* assertions)
{
  std::vector<Node> prepared;
  z3::Z3QuantifiersEngine::get(d_preprocContext->getTheoryEngine())
      ->prepareAssertions(assertions->ref(), prepared);
  // Each assertion gives at least one prepared formula, and the prepared
  // formulas keep the order of the assertions they come from.
  size_t n = assertions->size();
  Assert(prepared.size() >= n);
  for (size_t i = 0, psize = prepared.size(); i < psize; ++i)
  {
    if (i < n)
    {
      assertions->replace(i, prepared[i], nullptr, TrustId::UNKNOWN_PREPROCESS);
    }
    else
    {
      assertions->push_back(prepared[i]);
    }
  }
  // The skolem definitions are ordinary assertions for the decision
  // heuristic: the indices of the map refer to the assertions before
  // preparation.
  assertions->getIteSkolemMap().clear();
  return assertions->isInConflict() ? PreprocessingPassResult::CONFLICT
                                    : PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
