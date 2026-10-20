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
 *
 * Prepares the assertions for the ported Z3 core (--z3).
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__Z3_ASSERTION_PREPARATION_H
#define CVC5__PREPROCESSING__PASSES__Z3_ASSERTION_PREPARATION_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * The last preprocessing pass with --z3: it prepares the assertions for the
 * ported core, which the quantifiers engine owns (Z3QuantifiersEngine), and
 * asserts them to it; the prepared formulas replace the assertions, so that
 * cvc5 converts the same formulas the core takes.
 */
class Z3AssertionPreparation : public PreprocessingPass
{
 public:
  /**
   * The passes are made anew with each prop engine (see
   * ProcessAssertions::finishInit), right after it is initialized, and so
   * is the context of the core, which follows the prop engine's.
   */
  Z3AssertionPreparation(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__Z3_ASSERTION_PREPARATION_H */
