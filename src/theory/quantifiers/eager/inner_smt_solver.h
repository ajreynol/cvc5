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
 * It is a propagation-only CDCL(T): it does Boolean unit propagation over the
 * instance clauses, with InnerEGraph as its theory, and makes no decisions. A
 * conflict it finds is exported as a clause over the outer literals it used and
 * the quantified formulas whose instances it used, which is entailed by the
 * assertions however the inner solver derived it.
 *
 * See theory/quantifiers/eager/README.md section 6.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__INNER_SMT_SOLVER_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__INNER_SMT_SOLVER_H

#include <map>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/eager/inner_arith.h"
#include "theory/quantifiers/eager/inner_egraph.h"
#include "theory/quantifiers/eager/inst_queue.h"
#include "theory/quantifiers/eager/trail.h"
#include "theory/valuation.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersState;

namespace eager {

/**
 * The inner SMT solver.
 */
class InnerSmtSolver : protected EnvObj, public InstanceSink
{
 public:
  InnerSmtSolver(Env& env, Trail& trail, QuantifiersState& qs);
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
   * Do a round of reasoning over the instances and the current outer
   * assignment. Returns false if a conflict was found, in which case
   * getConflict is the clause to export.
   */
  bool check();

  /**
   * The conflict to export, valid after check returned false. It is a
   * disjunction of the negations of the outer literals used and of the
   * quantified formulas whose instances were used, hence is entailed by the
   * assertions no matter how it was derived internally.
   */
  Node getConflict() const { return d_conflict; }
  /** The literals the inner solver can propagate, with their explanations */
  const std::vector<std::pair<Node, Node>>& getPropagations() const
  {
    return d_propagations;
  }
  /** Forget the propagations that have been exported */
  void clearPropagations() { d_propagations.clear(); }
  /**
   * The instantiations the exported conflict and propagations rely on, as
   * (quantified formula, terms) pairs. Exporting a clause that mentions
   * (not q) has the effect of instantiating q, so cvc5's instantiation
   * bookkeeping has to be told about it, or a module that is responsible for q
   * will build its model as if q had not been instantiated.
   */
  const std::vector<std::pair<Node, std::vector<Node>>>& getUsedInstantiations()
      const
  {
    return d_usedInstantiations;
  }

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
    /** propagations exported */
    uint64_t d_numPropagations = 0;
    /** literals assigned, over all rounds */
    uint64_t d_numAssignments = 0;
  };
  const Stats& getStats() const { return d_stats; }

 private:
  /** A literal, i.e. an atom index together with a polarity */
  using LitId = size_t;
  static LitId mkLit(size_t atom, bool neg) { return 2 * atom + (neg ? 1 : 0); }
  static size_t litAtom(LitId l) { return l / 2; }
  static bool litNeg(LitId l) { return (l & 1) != 0; }
  static LitId litNot(LitId l) { return l ^ 1; }
  static constexpr LitId undefinedLit = static_cast<LitId>(-1);

  /** The value of an atom */
  enum class Value
  {
    UNDEF,
    TRUE,
    FALSE
  };
  /** Why a literal is assigned */
  enum class ReasonKind
  {
    /** it has this value in the outer solver */
    OUTER,
    /** it is the last unassigned literal of a clause */
    CLAUSE,
    /** the congruence closure implies it */
    THEORY
  };
  /** An atom of the inner problem */
  struct Atom
  {
    /** the formula */
    Node d_node;
    /** its value, if any */
    Value d_value = Value::UNDEF;
    /** the clauses it occurs in, in increasing order */
    std::vector<size_t> d_occurs;
    /** the term of the congruence closure it stands for */
    InnerEGraph::TermId d_term = InnerEGraph::undefinedTerm;
    /** for an equality, the two sides */
    InnerEGraph::TermId d_lhs = InnerEGraph::undefinedTerm;
    InnerEGraph::TermId d_rhs = InnerEGraph::undefinedTerm;
  };
  /** An element of the assignment trail */
  struct Assignment
  {
    LitId d_lit;
    ReasonKind d_kind;
    /** for CLAUSE */
    size_t d_clause = 0;
    /** for THEORY */
    std::vector<LitId> d_exp;
  };
  /** A clause of the inner problem */
  struct Clause
  {
    std::vector<LitId> d_lits;
    /** the instance it came from, or the number of instances if none */
    size_t d_instance;
  };
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
    /** the number of clauses and atoms before it was added */
    size_t d_numClauses;
    size_t d_numAtoms;
  };

  /** Retract the instances after the n^th */
  void retractInstancesFrom(size_t n);
  /** The index of the atom for the formula atom, creating it if needed */
  size_t getAtom(TNode atom);
  /** The literal for the formula lit, which may be a negation */
  LitId getLit(TNode lit);
  /** The formula of a literal */
  Node getLitNode(LitId l) const;
  /** The value of a literal */
  Value value(LitId l) const;
  /** Decompose a clause formula into literals */
  void getClauseLits(TNode body, std::vector<LitId>& lits);
  /** Add a clause, which belongs to the given instance */
  void addClause(const std::vector<LitId>& lits, size_t instance);

  /** Take the current value of the inner atoms from the outer solver */
  void syncOuter();
  /**
   * Take from the master equality engine the equalities and disequalities that
   * hold between the terms this solver knows about. The outer context entails
   * each of them, so each is sound as a root of an explanation, whatever the
   * reason the master equality engine had for it.
   */
  void syncOuterEqualities();
  /**
   * Assign l, with the given reason. Returns false if l was already false, in
   * which case the conflict explanation has been recorded.
   */
  bool assign(LitId l, ReasonKind kind, size_t clause, std::vector<LitId> exp);
  /** Tell the theory about a newly assigned literal */
  bool assertToTheory(LitId l);
  /** Propagate to a fixed point. Returns false on a conflict. */
  bool propagate();
  /** Look for literals the congruence closure implies. */
  bool theoryPropagate(bool& progress);
  /** Undo everything the current round assigned */
  void resetRound();
  /**
   * Collect the outer literals and the instances that the assignment of l
   * depends on.
   */
  void collectRoots(LitId l,
                    std::set<Node>& outerLits,
                    std::set<size_t>& instances,
                    std::unordered_set<LitId>& seen) const;
  /** Build the clause to export from a conflict explained by exp */
  Node mkConflict(const std::vector<LitId>& exp);
  /** Record that the exported clauses rely on these instances */
  void noteUsedInstances(const std::set<size_t>& instances);
  /** Assign the literal for atom with the given polarity as an outer fact */
  bool assignOuter(TNode atom, bool pol);
  /** The negation of the formula of a literal */
  static Node negate(TNode lit);

  /** The trail of the engine, used to retract instances on a pop */
  Trail& d_trail;
  /** The quantifiers state, used to read the outer assignment */
  QuantifiersState& d_qstate;
  /** The instances, in the order they were added */
  std::vector<Instance> d_instances;
  /** The congruence closure */
  InnerEGraph d_egraph;
  /** The arithmetic solver */
  InnerArith d_arith;
  /** The atoms of the inner problem */
  std::vector<Atom> d_atoms;
  /** Map from formulas to atom indices */
  std::map<Node, size_t> d_atomMap;
  /** The clauses of the inner problem */
  std::vector<Clause> d_clauses;
  /** The assignment of the current round, in order */
  std::vector<Assignment> d_assignTrail;
  /** The literals whose consequences have not been processed yet */
  std::vector<LitId> d_queue;
  /** The explanation of the conflict of the current round */
  std::vector<LitId> d_conflictExp;
  /** The clause the conflict came from, if any */
  size_t d_conflictClause;
  /** The terms true and false of the congruence closure */
  InnerEGraph::TermId d_trueTerm;
  InnerEGraph::TermId d_falseTerm;
  /** The checkpoint the current round started from */
  size_t d_roundCheckpoint;
  /** The conflict to export */
  Node d_conflict;
  /** The propagations to export, as (literal, explanation) pairs */
  std::vector<std::pair<Node, Node>> d_propagations;
  /** The instantiations the exported clauses rely on */
  std::vector<std::pair<Node, std::vector<Node>>> d_usedInstantiations;
  /** Statistics */
  Stats d_stats;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
