/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Remove rewrite rules, apply pre-skolemization to existential quantifiers.
 *
 * Calls the quantifier rewriter, removing rewrite rules and applying
 * pre-skolemization to existential quantifiers
 */

#include "preprocessing/passes/quantifiers_preprocess.h"

#include "base/output.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/quantifiers/quantifiers_preprocess.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace std;
using namespace cvc5::internal::theory;

QuantifiersPreprocess::QuantifiersPreprocess(
    PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "quantifiers-preprocess"),
      d_qp(new quantifiers::QuantifiersPreprocess(d_env))
{
}

QuantifiersPreprocess::~QuantifiersPreprocess() {}

PreprocessingPassResult QuantifiersPreprocess::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  size_t size = assertionsToPreprocess->size();
  for (size_t i = 0; i < size; ++i)
  {
    Node prev = (*assertionsToPreprocess)[i];
    TrustNode trn = d_qp->preprocess(prev);
    if (!trn.isNull())
    {
      assertionsToPreprocess->replaceTrusted(
          i, trn, TrustId::PREPROCESS_QUANTIFIERS_PP);
      assertionsToPreprocess->ensureRewritten(i);
      Trace("quantifiers-preprocess") << "*** Pre-skolemize " << prev << endl;
      Trace("quantifiers-preprocess")
          << "   ...got " << (*assertionsToPreprocess)[i] << endl;
      if (assertionsToPreprocess->isInConflict())
      {
        return PreprocessingPassResult::CONFLICT;
      }
    }
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
