/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The inner SMT solver, which owns the instances eager E-matching produces.
 *
 * Eager E-matching produces far more instances than the outer SAT solver
 * should see, and z3's instance lifecycle (add at a scope, drop when it is
 * popped, re-add later at a different cost threshold) does not map onto cvc5's
 * lemma channel, which is monotone and global. The instances therefore go into
 * this solver, whose state is deliberately separate from the rest of cvc5, and
 * which exports only the conflicts and propagations it derives.
 *
 * See theory/quantifiers/eager/README.md section 6.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__INNER_SMT_SOLVER_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__INNER_SMT_SOLVER_H

#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/eager/inner_arith.h"
#include "theory/quantifiers/eager/inner_egraph.h"
#include "theory/quantifiers/eager/inst_queue.h"
#include "theory/quantifiers/eager/trail.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

/**
 * The inner SMT solver.
 */
class InnerSmtSolver : protected EnvObj, public InstanceSink
{
 public:
  InnerSmtSolver(Env& env, Trail& trail);
  ~InnerSmtSolver();

  //---------------------------------------------------- InstanceSink
  /**
   * Take ownership of an instance. The instance is added at the current scope
   * and retracted when it is popped, as z3's qi_queue does with its instance
   * store.
   */
  void addInstance(TNode q,
                   const std::vector<Node>& terms,
                   TNode lemma,
                   uint32_t generation) override;
  //------------------------------------------------ end InstanceSink

  /**
   * Replay an assignment of the outer solver. Called for the facts asserted to
   * the quantifiers theory and for the equalities and disequalities the master
   * equality engine reports, so that the inner solver reasons relative to the
   * current outer assignment.
   */
  void notifyAssertedLit(TNode lit);

  /**
   * Do a round of reasoning over the instances and the replayed assignment.
   * Returns false if a conflict was found, in which case getConflict is the
   * clause to export.
   */
  bool check();

  /**
   * The conflict to export, valid after check returned false. It is a
   * disjunction of the negations of the outer literals used and of the
   * quantified formulas whose instances were used, hence is entailed by the
   * asserted formulas no matter how it was derived internally.
   */
  Node getConflict() const { return d_conflict; }
  /** The literals the inner solver can propagate, with their explanations */
  const std::vector<std::pair<Node, Node>>& getPropagations() const
  {
    return d_propagations;
  }
  /** Forget the propagations that have been exported */
  void clearPropagations() { d_propagations.clear(); }

  /** The number of instances currently held */
  size_t getNumInstances() const { return d_instances.size(); }
  /** Print the state of this solver */
  void debugPrint(std::ostream& out) const;

  /** Statistics, for -t eager-inst */
  struct Stats
  {
    /** instances added */
    uint64_t d_numInstances = 0;
    /** instances retracted */
    uint64_t d_numRetracted = 0;
    /** rounds of reasoning */
    uint64_t d_numChecks = 0;
    /** conflicts exported */
    uint64_t d_numConflicts = 0;
  };
  const Stats& getStats() const { return d_stats; }

 private:
  /** One instance held by this solver */
  struct Instance
  {
    /** the quantified formula it came from */
    Node d_quant;
    /** the terms substituted for its bound variables */
    std::vector<Node> d_terms;
    /** the clause, (or (not q) body) */
    Node d_lemma;
    /** the generation of the terms it introduces */
    uint32_t d_generation;
    /** the checkpoints to restore to when it is retracted */
    size_t d_egraphCheckpoint;
    size_t d_arithCheckpoint;
  };
  /** Retract the instances after the n^th */
  void retractInstancesFrom(size_t n);

  /** The trail of the engine, used to retract instances on a pop */
  Trail& d_trail;
  /** The instances, in the order they were added */
  std::vector<Instance> d_instances;
  /** The congruence closure */
  InnerEGraph d_egraph;
  /** The arithmetic solver */
  InnerArith d_arith;
  /** The literals of the outer assignment that have been replayed */
  std::vector<Node> d_assignment;
  /** The conflict to export */
  Node d_conflict;
  /** The propagations to export, as (literal, explanation) pairs */
  std::vector<std::pair<Node, Node>> d_propagations;
  /** Statistics */
  Stats d_stats;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
