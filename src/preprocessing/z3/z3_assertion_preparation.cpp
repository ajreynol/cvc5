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

#include "preprocessing/z3/z3_assertion_preparation.h"

#include "options/z3_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/quantifiers/theory_quantifiers.h"
#include "theory/theory_engine.h"
#include "z3/util/assertion_target.h"
#include "z3/util/ast.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

namespace {

/** The core, through the quantifiers engine of the quantifiers theory. */
z3::AssertionTarget* getTarget(TheoryEngine* te)
{
  theory::QuantifiersEngine* qe =
      static_cast<theory::quantifiers::TheoryQuantifiers*>(
          te->theoryOf(theory::THEORY_QUANTIFIERS))
          ->getOwnedQuantifiersEngine();
  z3::AssertionTarget* target = dynamic_cast<z3::AssertionTarget*>(qe);
  Assert(target != nullptr);
  return target;
}

}  // namespace

Z3AssertionPreparation::Z3AssertionPreparation(
    PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "z3-prep")
{
  if (options().z3.z3)
  {
    TheoryEngine* te = d_preprocContext->getTheoryEngine();
    getTarget(te)->resetCore(te);
  }
}

PreprocessingPassResult Z3AssertionPreparation::applyInternal(
    AssertionPipeline* assertions)
{
  z3::AssertionTarget* target = getTarget(d_preprocContext->getTheoryEngine());
  // the canonical variables the core and the E-matching engine expect; see
  // z3/util/ast.h
  z3::QuantifierNormalizer& norm = target->getNormalizer();
  for (size_t i = 0, n = assertions->size(); i < n; ++i)
  {
    Node res = norm.normalize((*assertions)[i]);
    target->assertPrepared(res);
    assertions->replace(i, res, nullptr, TrustId::UNKNOWN_PREPROCESS);
  }
  // The skolem definitions are ordinary assertions for the decision
  // heuristic, as they are for the core.
  assertions->getIteSkolemMap().clear();
  return assertions->isInConflict() ? PreprocessingPassResult::CONFLICT
                                    : PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
