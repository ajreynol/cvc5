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

#include "expr/node.h"
#include "z3/relevancy/theory_side.h"
#include "z3/util/trail.h"
#include "z3/util/types.h"

namespace cvc5::internal {
namespace z3 {

class PropCore;
class RelevancyPropagator;

/** An event handler invoked when an expression becomes relevant. */
class RelevancyEh
{
 public:
  virtual ~RelevancyEh() = default;

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
class SimpleRelevancyEh : public RelevancyEh
{
 public:
  SimpleRelevancyEh(TNode t) : d_target(t) {}
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
 * that an expression became relevant through relevantEh, and is told about new
 * assignments through assignEh.
 */
class RelevancyPropagator
{
 public:
  RelevancyPropagator(PropCore& core, TheorySide& theory);
  ~RelevancyPropagator();

  /** Install a handler invoked whenever n is marked as relevant. */
  void addHandler(TNode source, RelevancyEh* eh);

  /** Install a handler invoked whenever n is assigned to val. */
  void addWatch(TNode n, bool val, RelevancyEh* eh);

  /** Install a handler that marks target relevant when n is assigned val. */
  void addWatch(TNode n, bool val, TNode target);

  /** Called by SmtContext whenever an expression is assigned. */
  void assignEh(TNode n, bool val);

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

  /** Create a backtracking point. */
  void push();

  /** Backtrack. */
  void pop(size_t numScopes);

  /** The trail stack of the theory side, where the handlers live. */
  TrailStack& getTrailStack() const;

  template <typename Eh>
  RelevancyEh* mkRelevancyEh(const Eh& eh)
  {
    return new (getTrailStack()) Eh(eh);
  }

  /** Mark target relevant whenever src is marked relevant. */
  void addDependency(TNode src, TNode target);

  RelevancyEh* mkOrRelevancyEh(TNode n);
  RelevancyEh* mkImpliesRelevancyEh(TNode n);
  RelevancyEh* mkAndRelevancyEh(TNode n);
  RelevancyEh* mkIteRelevancyEh(TNode n);

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
  struct RelevancyEhs
  {
    RelevancyEh* d_head;
    RelevancyEhs* d_tail;
    RelevancyEhs(RelevancyEh* h, RelevancyEhs* t) : d_head(h), d_tail(t) {}
    RelevancyEh* head() const { return d_head; }
    RelevancyEhs* tail() const { return d_tail; }
  };

  /** A record of a handler installation, to be undone on backtracking. */
  struct EhTrail
  {
    enum class Kind
    {
      POS_WATCH,
      NEG_WATCH,
      HANDLER
    };
    Kind d_kind;
    Node d_node;
    EhTrail(TNode n) : d_kind(Kind::HANDLER), d_node(n) {}
    EhTrail(TNode n, bool val)
        : d_kind(val ? Kind::POS_WATCH : Kind::NEG_WATCH), d_node(n)
    {
    }
    Kind getKind() const { return d_kind; }
    TNode getNode() const { return d_node; }
  };

  struct Scope
  {
    size_t d_relevantExprsLim;
    size_t d_trailLim;
  };

  RelevancyEhs* getHandlers(TNode n) const;
  void setHandlers(TNode n, RelevancyEhs* ehs);
  RelevancyEhs* getWatches(TNode n, bool val) const;
  void setWatches(TNode n, bool val, RelevancyEhs* ehs);

  void setRelevant(TNode n);

  /** Unmark the expressions marked relevant since oldLim. */
  void unmarkRelevantExprs(size_t oldLim);
  void undoTrail(size_t oldLim);

  /** The propositional side, which owns this object. */
  PropCore& d_core;
  /** The theory side: equivalence classes, trail stack and statistics. */
  TheorySide& d_theory;
  size_t d_qhead;
  std::vector<Node> d_relevantExprs;
  /** Indexed by node id, true if the node is in d_relevantExprs. */
  std::vector<bool> d_isRelevant;
  std::unordered_map<TNode, RelevancyEhs*> d_relevantEhs;
  std::unordered_map<TNode, RelevancyEhs*> d_watches[2];
  /**
   * An over-approximating membership filter for d_watches, holding a superset
   * of the ids that have, or ever had, a watch list for the given phase. It is
   * monotonic -- never cleared on erase or pop -- so it can only yield false
   * positives. This lets getWatches skip the hash probe for the common
   * unwatched-literal case at the assignEh hotspot.
   */
  std::vector<bool> d_isWatched[2];
  std::vector<EhTrail> d_trail;
  std::vector<Scope> d_scopes;
  bool d_propagating;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__RELEVANCY__RELEVANCY_H */
