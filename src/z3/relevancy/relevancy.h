/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Relevancy propagation.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * files src/smt/smt_relevancy.h and src/smt/smt_relevancy.cpp, and recast in
 * cvc5 style. Z3's abstract propagator and its single implementation are
 * merged into one class here.
 *
 * Relevancy is the reason the Z3 core does far less quantifier instantiation
 * than a naive CDCL(T) engine: a term only becomes relevant when it is needed
 * to justify the current assignment, and only relevant terms take part in
 * E-matching. The propagation rules below decide, for each Boolean connective,
 * which of its arguments that makes necessary.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__RELEVANCY__RELEVANCY_H
#define CVC5__Z3__RELEVANCY__RELEVANCY_H

#include <ostream>
#include <unordered_map>
#include <vector>

#include "context/cdlist.h"
#include "expr/node.h"
#include "z3/relevancy/theory_side.h"
#include "z3/util/trail.h"
#include "z3/util/types.h"

namespace cvc5::internal {
namespace z3 {

class PropCore;
class RelevancyPropagator;

/** An event handler invoked when an expression becomes relevant. */
class RelevancyHandler
{
 public:
  virtual ~RelevancyHandler() = default;

  /** Invoked when n is marked as relevant. */
  virtual void operator()(RelevancyPropagator& rp, TNode /*n*/)
  {
    operator()(rp);
  }

  /** Invoked when atom is assigned to val. */
  virtual void operator()(RelevancyPropagator& rp, TNode /*atom*/, bool /*val*/)
  {
    operator()(rp);
  }

  /** The fallback for the two methods above. */
  virtual void operator()(RelevancyPropagator& rp) = 0;

 protected:
};

/** Marks a single target as relevant. */
class SimpleRelevancyHandler : public RelevancyHandler
{
 public:
  SimpleRelevancyHandler(TNode t) : d_target(t) {}
  void operator()(RelevancyPropagator& rp) override;

 private:
  TNode d_target;
};

/**
 * The relevancy propagator.
 *
 * Propagation constraints are declared with addHandler and addWatch; this
 * class also provides helpers for the constraints the internalizer needs.
 *
 * It uses the equivalence classes of the theory side (TheorySide), notifies it
 * that an expression became relevant through notifyRelevant, and is told about
 * new assignments through notifyAssigned.
 */
class RelevancyPropagator
{
 public:
  RelevancyPropagator(PropCore& core, TheorySide& theory);
  ~RelevancyPropagator();

  /** Install a handler invoked whenever n is marked as relevant. */
  void addHandler(TNode source, RelevancyHandler* eh);

  /** Install a handler invoked whenever n is assigned to val. */
  void addWatch(TNode n, bool val, RelevancyHandler* eh);

  /** Install a handler that marks target relevant when n is assigned val. */
  void addWatch(TNode n, bool val, TNode target);

  /** Called by SmtContext whenever an expression is assigned. */
  void notifyAssigned(TNode n, bool val);

  /** Mark the given expression as relevant. */
  void markAsRelevant(TNode n);

  /** True if the given expression is marked as relevant. */
  bool isRelevant(TNode n) const { return isRelevantCore(n); }

  bool isRelevantCore(TNode n) const
  {
    Assert(!n.isNull());
    size_t id = n.getId();
    return id < d_isRelevant.size() && d_isRelevant[id];
  }

  /**
   * Propagate relevancy, using the handlers installed by addHandler and
   * addWatch and the structure of the expressions already marked relevant.
   */
  void propagate();

  /** True if there is relevancy left to propagate. */
  bool canPropagate() const { return d_qhead < d_relevantExprs.size(); }

  /** The trail stack of the theory side, where the handlers live. */
  TrailStack& getTrailStack() const;

  template <typename Handler>
  RelevancyHandler* mkRelevancyHandler(const Handler& eh)
  {
    return new (getTrailStack()) Handler(eh);
  }

  /** Mark target relevant whenever src is marked relevant. */
  void addDependency(TNode src, TNode target);

  RelevancyHandler* mkOrRelevancyHandler(TNode n);
  RelevancyHandler* mkImpliesRelevancyHandler(TNode n);
  RelevancyHandler* mkAndRelevancyHandler(TNode n);
  RelevancyHandler* mkIteRelevancyHandler(TNode n);

  /** Marks the children of n as relevant. Requires n to be relevant. */
  void propagateRelevantApp(TNode n);
  /** The relevancy rule for a disjunction. */
  void propagateRelevantOr(TNode n);
  /** The relevancy rule for a conjunction. */
  void propagateRelevantAnd(TNode n);
  /** The relevancy rule for an implication. */
  void propagateRelevantImplies(TNode n);
  /** The relevancy rule for an if-then-else. */
  void propagateRelevantIte(TNode n);

 private:
  /** An immutable list of handlers, allocated in the trail stack. */
  struct RelevancyHandlers
  {
    RelevancyHandler* d_head;
    RelevancyHandlers* d_tail;
    RelevancyHandlers(RelevancyHandler* h, RelevancyHandlers* t)
        : d_head(h), d_tail(t)
    {
    }
    RelevancyHandler* head() const { return d_head; }
    RelevancyHandlers* tail() const { return d_tail; }
  };

  /** A record of a handler installation, to be undone on backtracking. */
  struct HandlerTrail
  {
    enum class Kind
    {
      POS_WATCH,
      NEG_WATCH,
      HANDLER
    };
    Kind d_kind;
    Node d_node;
    HandlerTrail(TNode n) : d_kind(Kind::HANDLER), d_node(n) {}
    HandlerTrail(TNode n, bool val)
        : d_kind(val ? Kind::POS_WATCH : Kind::NEG_WATCH), d_node(n)
    {
    }
    Kind getKind() const { return d_kind; }
    TNode getNode() const { return d_node; }
  };

  /** Unmarks an expression marked relevant when it is popped. */
  struct UnmarkCleanup
  {
    RelevancyPropagator* d_rp;
    void operator()(Node& n) { d_rp->d_isRelevant[n.getId()] = false; }
  };

  /** Undoes a handler installation when it is popped. */
  struct UndoHandlerCleanup
  {
    RelevancyPropagator* d_rp;
    void operator()(HandlerTrail& t) { d_rp->undoHandler(t); }
  };

  RelevancyHandlers* getHandlers(TNode n) const;
  void setHandlers(TNode n, RelevancyHandlers* ehs);
  RelevancyHandlers* getWatches(TNode n, bool val) const;
  void setWatches(TNode n, bool val, RelevancyHandlers* ehs);

  void setRelevant(TNode n);

  /** Undo the handler installation t. */
  void undoHandler(const HandlerTrail& t);

  /** The propositional side, which owns this object. */
  PropCore& d_core;
  /** The theory side: equivalence classes, trail stack and statistics. */
  TheorySide& d_theory;
  /**
   * The next expression of d_relevantExprs to propagate. It is not popped:
   * a pop leaves it past the end, and it is moved back to the end when an
   * expression is added.
   */
  size_t d_qhead;
  /** Indexed by node id, true if the node is in d_relevantExprs. */
  std::vector<bool> d_isRelevant;
  std::unordered_map<TNode, RelevancyHandlers*> d_relevantHandlers;
  std::unordered_map<TNode, RelevancyHandlers*> d_watches[2];
  /**
   * An over-approximating membership filter for d_watches, holding a superset
   * of the ids that have, or ever had, a watch list for the given phase. It is
   * monotonic -- never cleared on erase or pop -- so it can only yield false
   * positives. This lets getWatches skip the hash probe for the common
   * unwatched-literal case at the notifyAssigned hotspot.
   */
  std::vector<bool> d_isWatched[2];
  /**
   * The expressions marked relevant, and the handler installations, in the
   * context of the trail stack. Their cleanups use the fields above, so they
   * are declared after them.
   */
  context::CDList<Node, UnmarkCleanup> d_relevantExprs;
  context::CDList<HandlerTrail, UndoHandlerCleanup> d_trail;
  bool d_propagating;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__RELEVANCY__RELEVANCY_H */
