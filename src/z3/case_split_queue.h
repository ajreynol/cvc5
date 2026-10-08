/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The case split queue, which decides what the search branches on next.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_case_split_queue.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__CASE_SPLIT_QUEUE_H
#define CVC5__Z3__CASE_SPLIT_QUEUE_H

#include <ostream>

#include "expr/node.h"
#include "z3/params.h"
#include "z3/types.h"
#include "z3/util/literal.h"

namespace cvc5::internal {
namespace z3 {

class SmtContext;

/** An abstract case split queue. */
class CaseSplitQueue
{
 public:
  virtual ~CaseSplitQueue() = default;

  virtual void activityIncreasedEh(BoolVar v) = 0;
  virtual void activityDecreasedEh(BoolVar v) = 0;
  virtual void mkVarEh(BoolVar v) = 0;
  virtual void delVarEh(BoolVar v) = 0;
  virtual void assignLitEh(Literal l) {}
  virtual void unassignVarEh(BoolVar v) = 0;
  virtual void relevantEh(TNode n) = 0;
  virtual void initSearchEh() = 0;
  virtual void endSearchEh() = 0;
  virtual void internalizeInstanceEh(TNode e, uint32_t gen) {}
  virtual void reset() = 0;
  virtual void pushScope() = 0;
  virtual void popScope(size_t numScopes) = 0;
  /**
   * The next variable to branch on, or s_nullBoolVar if there is none, and
   * the phase to try first, or L_UNDEF to let the phase heuristic decide.
   */
  virtual void nextCaseSplit(BoolVar& next, LBool& phase) = 0;
  virtual void print(std::ostream& out) = 0;

  /** A theory-aware branching hint. */
  virtual void addTheoryAwareBranchingInfo(BoolVar v,
                                           double priority,
                                           LBool phase)
  {
  }
};

/**
 * Build the case split queue selected by p.d_caseSplitStrategy. As in Z3, a
 * relevancy-based strategy is downgraded to plain activity if relevancy is
 * disabled or auto configuration is on.
 */
CaseSplitQueue* mkCaseSplitQueue(SmtContext& ctx, Params& p);

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__CASE_SPLIT_QUEUE_H */
