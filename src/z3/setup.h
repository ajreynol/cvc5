/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Configuration of the ported Z3 core: which theories are registered and
 * which parameters are overridden, based on the logic and on the static
 * features of the input.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), files
 * src/smt/smt_setup.cpp and the per-logic setup methods of
 * src/params/smt_params.cpp, recast in cvc5 style.
 *
 * This matters as much as the search code: with auto configuration on, which
 * is Z3's default, a quantified problem is solved with phase selection
 * "always false", geometric restarts with factor 1.5, an eager instantiation
 * threshold of 7 rather than 10, and model based instantiation enabled. The
 * numbers here are Z3's.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__SETUP_H
#define CVC5__Z3__SETUP_H

#include <cstdint>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "z3/params.h"
#include "z3/smt_context.h"

namespace cvc5::internal {
namespace z3 {

/**
 * The static features of the input that the configuration keys on. This is
 * the subset of Z3's static_features that the branches reachable from the
 * logics in scope actually consult.
 */
struct StaticFeatures
{
  size_t d_numQuantifiers = 0;
  size_t d_numQuantifiersWithPatterns = 0;
  size_t d_numNonLinear = 0;
  bool d_hasInt = false;
  bool d_hasReal = false;
  bool d_hasBv = false;
  bool d_hasArrays = false;
  bool d_hasDatatypes = false;
  bool d_hasUf = false;
  bool d_hasStrings = false;
  bool d_hasFp = false;

  /** Collect the features of the given formulas. */
  void collect(const std::vector<Node>& fmls);

 private:
  void collect(TNode n, std::unordered_set<Node>& visited);
};

/** Configure the given context. This is Z3's smt::setup. */
class Setup
{
 public:
  Setup(SmtContext& ctx, Params& p);

  /** Configure according to the given mode. */
  void operator()(ConfigMode cm);

 private:
  void setupDefault();
  void setupAutoConfig();
  void setupUnknown();
  void setupUnknown(const StaticFeatures& st);
  void setupRelevancy(const StaticFeatures& st);

  void setupQfUf();
  void setupAuflia(bool simpleArray);
  void setupAuflia(const StaticFeatures& st);
  void setupAuflira(bool simpleArray);

  void setupArith();
  void setupBv();
  void setupDatatypes();

  SmtContext& d_ctx;
  Params& d_params;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__SETUP_H */
