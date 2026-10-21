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
 * Not ported from Z3: this is cvc5 integration code, which sequences the
 * ported normalizations of this directory in the order Z3's own
 * preprocessing applies them.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__Z3__Z3_ASSERTION_PREPARATION_H
#define CVC5__PREPROCESSING__Z3__Z3_ASSERTION_PREPARATION_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * The last preprocessing pass with --z3, the stage between cvc5's
 * preprocessing and the ported core, which the quantifiers engine owns
 * (Z3QuantifiersEngine). It establishes the invariants the core inherits
 * from Z3's own preprocessing (asserted_formulas::reduce()) and that cvc5's
 * preprocessing does not: each assertion is given the canonical variables
 * and asserted to the core, and replaces the assertion, so that cvc5
 * converts the formulas the core takes. The assertions are already in the
 * form cvc5's theories take, since the renaming changes only the quantified
 * formulas, which theory preprocessing leaves as they are.
 *
 * Z3's negation normal form is not needed: the existentials nested in
 * universal quantifiers are skolemized by cvc5's pre-skolemization, which
 * --z3 enables (--pre-skolem-quant=agg), and the core has cvc5 skolemize the
 * quantified formulas it assigns false.
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

#endif /* CVC5__PREPROCESSING__Z3__Z3_ASSERTION_PREPARATION_H */
