/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Eager quantifiers matching
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__EAGER_QMATCHING_H
#define CVC5__PREPROCESSING__PASSES__EAGER_QMATCHING_H

#include "preprocessing/preprocessing_pass.h"
#include "proof/rewrite_proof_generator.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class EagerQMatching : public PreprocessingPass
{
 public:
  EagerQMatching(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  void processInternal(const Node& a);
  std::unordered_set<Node> d_visited;
  std::map<Node, std::vector<Node> > d_ufTerms;
  std::vector<Node> d_tlQuant;
  class PatInfo
  {
   public:
    PatInfo() : d_ufIndex(0) {}
    Node d_quant;
    size_t d_ufIndex;
  };
  std::map<Node, PatInfo> d_pinfo;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__EAGER_QMATCHING_H */
