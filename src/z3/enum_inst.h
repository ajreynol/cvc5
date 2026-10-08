/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Enumerative quantifier instantiation.
 *
 * This is NOT ported from Z3. Z3 answers the question "what now?" when
 * E-matching runs out of matches with model based quantifier instantiation,
 * which its setup enables for every quantified logic: the model checker finds
 * a binding the candidate model falsifies and the search restarts with the
 * new instance (see smt_model_finder.cpp and smt_model_checker.cpp). Porting
 * that would mean porting Z3's whole model construction stack -- proto
 * models, value factories and the model evaluator -- which is out of
 * proportion to what it contributes to quantifier *performance*.
 *
 * What is here instead is the mechanism cvc5 itself uses for the same
 * purpose: once E-matching is exhausted, each quantifier is instantiated with
 * tuples of the terms already in the context, in a deterministic order, one
 * instance per quantifier per final check. Bindings the current assignment
 * already falsifies are preferred, which is the part that plays the role of
 * Z3's model checker.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__ENUM_INST_H
#define CVC5__Z3__ENUM_INST_H

#include <map>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"
#include "z3/quick_checker.h"
#include "z3/types.h"

namespace cvc5::internal {
namespace z3 {

class SmtContext;

class EnumInst
{
 public:
  /**
   * @param useFallback Whether a binding that the current assignment does not
   * falsify may be used when no falsified one is found. Z3's model checker
   * only ever adds a falsified instance, but its model is complete while the
   * assignment here is partial, so the weaker criterion finds more.
   */
  EnumInst(SmtContext& ctx, size_t maxPerRound);

  /**
   * Add at most one instance for each of the given quantifiers. Returns true
   * if an instance was added, in which case the search is not done.
   */
  bool instantiate(const std::vector<Node>& quantifiers);

 private:
  SmtContext& d_context;
  QuickChecker d_checker;
  /** how many instances one final check may add */
  size_t d_maxPerRound;
  /** the quantifier the next round starts at */
  size_t d_qIdx;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__ENUM_INST_H */
