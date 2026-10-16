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
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), files
 * src/params/smt_params.h and src/params/qi_params.h, and recast in cvc5
 * style. The default values are Z3's, verbatim: they are part of what is
 * being replicated, so they are kept here rather than being re-derived from
 * cvc5's own defaults. Only the parameters of the quantifier stack are
 * ported; the --z3-qi-* options set some of them.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__PARAMS_H
#define CVC5__Z3__PARAMS_H

#include <climits>
#include <cstdint>
#include <string>

namespace cvc5::internal {

class Options;

namespace z3 {

/** The parameters of the core. */
struct Params
{
  /** Set the parameters the options of opts set. */
  void initialize(const Options& opts);

  // ---------------------------------------------------- quantifier
  // instantiation
  /**
   * The cost of a quantifier instantiation, as an arithmetic expression over
   * "weight", "generation", "cost", "min_top_generation" and
   * "max_top_generation". Instances above d_qiEagerThreshold are delayed and
   * those above d_qiLazyThreshold are dropped.
   *
   * The default must keep weight > 0 contributing, otherwise matching loops
   * are never broken; see the long comment in Z3's qi_params.h.
   */
  std::string d_qiCost = "(+ weight generation)";
  /** How the generation of enodes created by an instantiation is set. */
  std::string d_qiNewGen = "cost";
  double d_qiEagerThreshold = 10.0;
  double d_qiLazyThreshold = 20.0;
  uint32_t d_qiMaxEagerMultipatterns = 0;
  uint32_t d_qiMaxLazyMultipatternMatching = 2;
  bool d_qiPromoteUnsat = true;
  uint32_t d_qiMaxInstances = UINT_MAX;

  // ---------------------------------------------------- pattern inference
  /** How arithmetic symbols may be used in an inferred pattern. */
  enum ArithPatternInferenceKind
  {
    /** do not infer patterns with arithmetic terms */
    AP_NO,
    /** infer patterns with arithmetic terms only if there is no other option */
    AP_CONSERVATIVE,
    /** always use patterns with arithmetic terms */
    AP_FULL
  };

  bool d_piEnabled = true;
  uint32_t d_piMaxMultiPatterns = 0;
  bool d_piBlockLoopPatterns = true;
  bool d_piDecomposePatterns = true;
  ArithPatternInferenceKind d_piArith = AP_CONSERVATIVE;
  uint32_t d_piArithWeight = 5;
  uint32_t d_piNonNestedArithWeight = 10;
  int32_t d_piNopatWeight = -1;
  bool d_piAvoidSkolems = true;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__PARAMS_H */
