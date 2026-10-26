/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The interface of the theory side of the ported Z3 core, as the Boolean
 * side sees it.
 *
 * Not ported from Z3: in Z3, smt::context is one class; here the Boolean
 * side (PropCore, RelevancyPropagator) reaches the theory side (SmtContext)
 * only through this interface.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__RELEVANCY__THEORY_SIDE_H
#define CVC5__Z3__RELEVANCY__THEORY_SIDE_H

#include "expr/node.h"
#include "z3/util/literal.h"
#include "z3/util/types.h"

namespace cvc5::internal {
namespace z3 {

class TrailStack;
struct Statistics;
class Trail;

/**
 * The theory side of the core, which owns the Boolean side: the E-graph,
 * the theories and the quantifiers. See SmtContext.
 */
class TheorySide
{
 public:
  virtual ~TheorySide() = default;

  // ------------------------------------- the scheduling and backtracking
  //                                       contract
  /**
   * Propagate on the theory side, after Boolean propagation and relevancy
   * have saturated. Returns false on a conflict.
   */
  virtual bool theoryPropagate() = 0;
  /** Whether the theory side has propagation work pending. */
  virtual bool hasPendingTheoryWork() const = 0;
  /** Called at the start of a search. */
  virtual void initSearchEh() = 0;
  /** The final check, when every relevant Boolean variable is assigned. */
  virtual FinalCheckStatus finalCheck() = 0;
  /** Push a scope of the theory side, after the Boolean side's. */
  virtual void pushTheoryScope() = 0;
  /** Pop numScopes scopes, before the Boolean variables are unassigned. */
  virtual void popTheoryScopeBegin(size_t numScopes) = 0;
  /** Pop numScopes scopes, after the Boolean variables are unassigned. */
  virtual void popTheoryScopeEnd(size_t numScopes) = 0;
  /** Whether the search is to stop. */
  virtual bool getCancelFlag() = 0;

  // ------------------------------------------------------ internalization
  /** Internalize the asserted formula n, of the given generation. */
  virtual void internalizeAssertion(TNode n, uint32_t generation) = 0;
  /** Internalize n, in a gate context or not. */
  virtual void internalize(TNode n, bool gateCtx) = 0;
  /** Internalize n and its subterms, in a gate context or not. */
  virtual void internalizeRec(TNode n, bool gateCtx) = 0;
  /** Record the generation of n's subterms, at the scope level given. */
  virtual void cacheGeneration(TNode n, uint32_t newScopeLvl) = 0;
  /** Forget the terms recorded by cacheGeneration. */
  virtual void resetCacheGeneration() = 0;
  /** The Boolean variable of n was deleted. */
  virtual void notifyBoolVarDeleted(TNode n) = 0;

  // ------------------------------------------------------- notifications
  /** The atom of l was assigned: propagate it on the theory side. */
  virtual void enqueueAtom(Literal l) = 0;
  /** n became relevant. */
  virtual void relevantEh(TNode n) = 0;

  // ------------------------------------------------------------ utilities
  /**
   * The term after n in its equivalence class (n itself for a singleton),
   * or null if n is not a term of the E-graph.
   */
  virtual TNode getNextInEClass(TNode n) const = 0;
  /** Push an undo object on the trail of the theory side. */
  virtual void pushTrailPtr(Trail* ptr) = 0;
  /** The trail stack, where the relevancy handlers live. */
  virtual TrailStack& getTrailStack() = 0;
  /** The statistics of the core. */
  virtual Statistics& getStats() = 0;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__RELEVANCY__THEORY_SIDE_H */
