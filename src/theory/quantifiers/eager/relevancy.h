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
 * Ported from Z3: src/smt/smt_relevancy.h, src/smt/smt_relevancy.cpp.
 * Z3 is Copyright (c) Microsoft Corporation and licensed under the MIT
 * License, see licenses/z3-LICENSE.
 *
 * Z3's abstract propagator and its single implementation are merged into one
 * class here.
 *
 * Relevancy is the reason the Z3 core does far less quantifier instantiation
 * than a naive CDCL(T) engine: a term only becomes relevant when it is needed
 * to justify the current assignment, and only relevant terms take part in
 * E-matching. The propagation rules below decide, for each Boolean connective,
 * which of its arguments that makes necessary.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__RELEVANCY_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__RELEVANCY_H

#include <ostream>
#include <unordered_map>
#include <vector>

#include "context/cdlist.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

class EGraph;
class PropCore;
class TrailStack;
struct Statistics;

/**
 * The relevancy propagator.
 *
 * An expression marked relevant makes its arguments relevant by the rule of
 * its kind (propagateRelevantGate), and the expressions that depend on it
 * (addDependency). A gate whose rule depends on the values of its arguments
 * watches them (addGateWatch), and its rule is applied again when one is
 * assigned. Relevancy is shared by an entire equivalence class of the
 * E-graph: marking an expression marks its class, and merging a relevant
 * class with another marks the other (notifyMerge).
 *
 * It notifies PropCore that an expression became relevant through
 * notifyRelevant, and is told about new assignments through notifyAssigned.
 */
class RelevancyPropagator
{
 public:
  /**
   * Make the propagator of core, over the classes of egraph, backtracked
   * through trail, recording into stats. It only stores egraph, which may
   * still be under construction.
   */
  RelevancyPropagator(PropCore& core,
                      EGraph& egraph,
                      TrailStack& trail,
                      Statistics& stats);
  ~RelevancyPropagator();

  /** Mark target relevant whenever src is marked relevant. */
  void addDependency(TNode src, TNode target);

  /**
   * Apply the rule of the gate n (an and, or, implies or ite) again, if n is
   * relevant, when the expression child is assigned val.
   */
  void addGateWatch(TNode child, bool val, TNode gate);

  /** Called by PropCore whenever an expression is assigned. */
  void notifyAssigned(TNode n, bool val);

  /**
   * The classes of n1 and n2 merge: if either is relevant, the other becomes
   * relevant.
   */
  void notifyMerge(TNode n1, TNode n2);

  /** Mark the given expression, and its equivalence class, as relevant. */
  void markAsRelevant(TNode n);

  /** True if the given expression is marked as relevant. */
  bool isRelevant(TNode n) const
  {
    Assert(!n.isNull());
    size_t id = n.getId();
    return id < d_isRelevant.size() && d_isRelevant[id];
  }

  /**
   * Propagate relevancy, using the dependencies, the gate watches and the
   * structure of the expressions already marked relevant.
   */
  void propagate();

  /** True if there is relevancy left to propagate. */
  bool canPropagate() const { return d_qhead < d_relevantExprs.size(); }

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
  /** The relevancy rule for n, by its kind. */
  void propagateRelevantGate(TNode n);

 private:
  /**
   * An edge added by addDependency (to d_dependents) or addGateWatch (to
   * d_gateWatches), to be removed on backtracking.
   */
  struct Edge
  {
    /** Which map the edge is in. */
    enum class Kind
    {
      /** A gate watch for the value true. */
      POS_WATCH,
      /** A gate watch for the value false. */
      NEG_WATCH,
      /** A dependency. */
      DEPENDENCY
    };
    /** The kind of the edge. */
    Kind d_kind;
    /** The source of the edge: the watched or depended-on expression. */
    Node d_node;
  };

  /** Unmarks an expression marked relevant when it is popped. */
  struct UnmarkCleanup
  {
    /** The owner of the list. */
    RelevancyPropagator* d_rp;
    /** Unmark n. */
    void operator()(Node& n) { d_rp->d_isRelevant[n.getId()] = false; }
  };

  /** Removes an edge when it is popped. */
  struct RemoveEdgeCleanup
  {
    /** The owner of the list. */
    RelevancyPropagator* d_rp;
    /** Remove e. */
    void operator()(Edge& e) { d_rp->removeEdge(e); }
  };

  /**
   * The expressions of n in edges, newest first, as they are notified. They
   * are copied, since notifying them may add edges.
   */
  static std::vector<TNode> getEdges(
      const std::unordered_map<TNode, std::vector<TNode>>& edges, TNode n);

  /**
   * Mark n alone relevant, queue it for propagate, and notify PropCore.
   * Requires n not to be relevant.
   */
  void setRelevant(TNode n);

  /** Remove the edge e, the last one added for its node. */
  void removeEdge(const Edge& e);

  /** The propositional side, which owns this object. */
  PropCore& d_core;
  /** The E-graph, whose classes relevancy is shared by. */
  EGraph& d_egraph;
  /** The statistics of the core. */
  Statistics& d_stats;
  /**
   * The next expression of d_relevantExprs to propagate. It is not popped:
   * a pop leaves it past the end, and it is moved back to the end when an
   * expression is added.
   */
  size_t d_qhead;
  /** Indexed by node id, true if the node is in d_relevantExprs. */
  std::vector<bool> d_isRelevant;
  /** For each expression, the expressions that depend on it, oldest first. */
  std::unordered_map<TNode, std::vector<TNode>> d_dependents;
  /**
   * For each expression and value (index 1 for true), the gates that watch
   * it, oldest first.
   */
  std::unordered_map<TNode, std::vector<TNode>> d_gateWatches[2];
  /**
   * An over-approximating membership filter for d_gateWatches, holding a
   * superset of the ids that have, or ever had, a watch for the given value.
   * It is monotonic -- never cleared on erase or pop -- so it can only yield
   * false positives. This lets getWatches skip the hash probe for the common
   * unwatched-literal case at the notifyAssigned hotspot.
   */
  std::vector<bool> d_isWatched[2];
  /**
   * The expressions marked relevant, and the edges added, in the context of
   * the trail stack. Their cleanups use the fields above, so they are
   * declared after them.
   */
  context::CDList<Node, UnmarkCleanup> d_relevantExprs;
  /** The edges added, see Edge. */
  context::CDList<Edge, RemoveEdgeCleanup> d_edges;
  /** True while propagate runs, so that a nested call returns at once. */
  bool d_propagating;
};

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER__RELEVANCY_H */
