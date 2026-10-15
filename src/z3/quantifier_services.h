/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * What the quantifier stack uses of the theory side.
 *
 * Not ported from Z3, where the quantifier stack calls smt::context
 * directly: this is the outbound half of the contract of the stack, which
 * Phase C of THEORY_BRANCH.md extracts.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__QUANTIFIER_SERVICES_H
#define CVC5__Z3__QUANTIFIER_SERVICES_H

#include <string>
#include <utility>
#include <vector>

#include "expr/node.h"
#include "z3/types.h"
#include "z3/util/trail.h"

namespace cvc5::internal {

class Env;

namespace z3 {

class Region;
struct Params;
struct Statistics;

/**
 * The services the quantifier stack (QuantifierManager and its plugin, the
 * matcher Mam, the instance queue QiQueue, Checker, QuickChecker and
 * EnumInst) uses of the theory side, which SmtContext implements. The stack
 * calls nothing else of the theory side; it reads enodes directly.
 *
 * The inbound half of the contract is QuantifierManager's interface: the
 * theory side tells it when a quantifier is asserted or deleted, when an
 * enode becomes relevant, when two classes merge, and when to propagate, to
 * run a final check, to push, to pop and to restart.
 */
class QuantifierServices
{
 public:
  virtual ~QuantifierServices() = default;

  // ------------------------------------------------------------ term view
  /** Whether n has an enode. */
  virtual bool eInternalized(TNode n) const = 0;
  /** The enode of n, which must have one. */
  virtual ENode* getENode(TNode n) const = 0;
  /** All enodes, in the order of their creation. */
  virtual const ENodeVector& enodes() const = 0;
  /** The enodes of the applications of decl. */
  virtual const ENodeVector& enodesOf(TNode decl) const = 0;
  virtual size_t getNumENodesOf(TNode decl) const = 0;
  /** A dense id for decl, created on demand. */
  virtual uint32_t getDeclId(TNode decl) = 0;
  /** The dense id of decl, or UINT32_MAX if it has none yet. */
  virtual uint32_t getDeclIdOption(TNode decl) const = 0;
  /** An enode congruent to decl(args), or null if there is none. */
  virtual ENode* getENodeEqTo(TNode decl,
                              bool commutative,
                              size_t numArgs,
                              ENode* const* args) = 0;
  virtual bool isDiseq(ENode* n1, ENode* n2) const = 0;
  /** The generation of the class of e. */
  virtual uint32_t getGeneration(ENode* e) const = 0;
  virtual uint32_t getMaxGeneration(size_t numENodes,
                                    ENode* const* enodes) = 0;
  /** The value of the class of n, if it has one. */
  virtual bool getValue(ENode* n, Node& value) = 0;
  /** Internalize the ground term n of a pattern. */
  virtual void internalize(TNode n, bool gateCtx, uint32_t generation) = 0;

  // --------------------------------------------------------- Boolean view
  virtual LBool getAssignment(TNode n) const = 0;
  virtual bool bInternalized(TNode n) const = 0;
  virtual bool litInternalized(TNode n) const = 0;
  virtual bool inconsistent() const = 0;
  virtual uint32_t getScopeLevel() const = 0;
  /** Whether the stack may add instances now (not in a conflict). */
  virtual bool canPropagate() const = 0;

  // ------------------------------------------------------- relevance view
  virtual bool relevancy() const = 0;
  virtual bool isRelevant(TNode n) const = 0;
  /** Whether E-matching considers n (--z3-relevancy-match). */
  virtual bool isRelevantForMatching(ENode* n) const = 0;
  /** Whether the instance checkers consider n (--z3-relevancy-check). */
  virtual bool isRelevantForChecking(TNode n) const = 0;
  virtual bool isRelevantForChecking(ENode* n) const = 0;
  virtual void markAsRelevant(ENode* n) = 0;

  // -------------------------------------------------------- instance sink
  /** Rewrite an instance before it is internalized. */
  virtual Node rewriteInstance(TNode n) const = 0;
  /**
   * Internalize the body of an instance with its generation; see
   * SmtContext::internalizeInstance.
   */
  virtual bool internalizeInstance(TNode body,
                                   uint32_t generation,
                                   Node& root) = 0;
  /** Make a permanent instance a root again (--z3-qi-permanent-local). */
  virtual void reactivateInstance(TNode root) = 0;

  // ------------------------------------------------------- infrastructure
  virtual Statistics& getStats() = 0;
  virtual Params& getParams() = 0;
  virtual const Env& getEnv() const = 0;
  /** The region that lives as long as the context. */
  virtual Region& getRegion() = 0;
  /** The trail of both sides, undone when scopes are popped. */
  virtual TrailStack& getTrailStack() = 0;
  template <typename TrailObject>
  void pushTrail(const TrailObject& obj)
  {
    getTrailStack().push(obj);
  }
  virtual bool getCancelFlag() = 0;
  virtual bool resourceLimitsExceeded() = 0;
  virtual void setReasonUnknown(const std::string& msg) = 0;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIER_SERVICES_H */
