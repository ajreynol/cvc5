/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Parameters of the ported Z3 SMT core.
 */

#include "z3/params.h"

#include "options/options.h"
#include "options/z3_options.h"

namespace cvc5::internal {
namespace z3 {

void Params::initialize(const Options& opts)
{
  // The defaults of the options are the values Verus passes to Z3
  // (smt.qi.eager_threshold=100).
  d_qiCost = opts.z3.z3QiCost;
  d_qiNewGen = opts.z3.z3QiNewGen;
  d_qiEagerThreshold = opts.z3.z3QiEagerThreshold;
  d_qiLazyThreshold = opts.z3.z3QiLazyThreshold;
  d_qiMaxEagerMultipatterns =
      static_cast<uint32_t>(opts.z3.z3QiMaxMultiPatterns);
  uint64_t maxInst = opts.z3.z3QiMaxInstances;
  d_qiMaxInstances =
      maxInst > UINT32_MAX ? UINT32_MAX : static_cast<uint32_t>(maxInst);
}

}  // namespace z3
}  // namespace cvc5::internal
