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
#include "preprocessing/z3/nnf.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * The last preprocessing pass with --z3, the stage between cvc5's
 * preprocessing and the ported core, which the quantifiers engine owns
 * (Z3QuantifiersEngine). It establishes the invariants the core inherits
 * from Z3's own preprocessing (asserted_formulas::reduce()) and that cvc5's
 * preprocessing does not. In order, each assertion is converted to negation
 * normal form, naming the quantifiers below atoms, after which each
 * definition introduced by the naming and then the formula itself is given
 * the canonical variables, put in the form cvc5's theories take, and
 * asserted to the core. The prepared formulas replace the
 * assertions, so that cvc5 converts the formulas the core takes.
 *
 * With --no-z3-assertion-preparation, the negation normal form is skipped.
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

 private:
  /**
   * Z3's nnf pass, which leaves every universal quantifier in a positive
   * position, as the core relies on.
   */
  z3::Nnf d_nnf;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__Z3__Z3_ASSERTION_PREPARATION_H */
