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
 * The solver is incremental: what it derives stays until the scope it was
 * derived at is popped, and each round only processes what changed since the
 * previous one.
 * See theory/quantifiers/eager/README.md section 6.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__INNER_SMT_SOLVER_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__INNER_SMT_SOLVER_H

#include <map>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/eager/egraph.h"
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
 *
 * It listens to the e-graph mirror to learn which of its terms are equal or
 * disequal in the outer solver, and to its own congruence closure to learn
 * which atoms a merge may imply.
 */
class InnerSmtSolver : protected EnvObj,
                       public InstanceSink,
                       public EGraphListener,
                       public InnerEGraphListener
{
 public:
  InnerSmtSolver(Env& env, Trail& trail, QuantifiersState& qs, EGraph& mirror);
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

  //-------------------------------------------------- EGraphListener
  /** A term of the outer solver appeared, which may be one of ours */
  void notifyNewENode(ENode* e) override;
  /** Two classes of the outer solver are about to be merged */
  void notifyPreMerge(ENode* r1, ENode* r2) override;
  /** Two classes of the outer solver were asserted disequal */
  void notifyDiseq(ENode* e1, ENode* e2) override;
  //---------------------------------------------- end EGraphListener

  //--------------------------------------------- InnerEGraphListener
  /** Our congruence closure is about to merge the class of a into that of b */
  void notifyMerge(size_t a, size_t b) override;
  //----------------------------------------- end InnerEGraphListener

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
    /** equalities and disequalities taken from the outer solver */
    uint64_t d_numOuterFacts = 0;
  };
  const Stats& getStats() const { return d_stats; }

 private:
  /** A literal, i.e. an atom index together with a polarity */
  using LitId = size_t;
  using TermId = InnerEGraph::TermId;
  static LitId mkLit(size_t atom, bool neg) { return 2 * atom + (neg ? 1 : 0); }
  static size_t litAtom(LitId l) { return l / 2; }
  static bool litNeg(LitId l) { return (l & 1) != 0; }
  static LitId litNot(LitId l) { return l ^ 1; }
  static constexpr LitId undefinedLit = static_cast<LitId>(-1);
  static constexpr size_t noIndex = static_cast<size_t>(-1);

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
    /** if assigned, its position in d_assignTrail */
    size_t d_trailIndex = noIndex;
    /** the clauses it occurs in, in increasing order */
    std::vector<size_t> d_occurs;
    /** the term of the congruence closure it stands for */
    TermId d_term = InnerEGraph::undefinedTerm;
    /** for an equality, the two sides */
    TermId d_lhs = InnerEGraph::undefinedTerm;
    TermId d_rhs = InnerEGraph::undefinedTerm;
    /**
     * Whether this atom stands for a Boolean connective whose defining clauses
     * have been added, i.e. whether it is a Tseitin definition rather than a
     * theory atom.
     */
    bool d_defined = false;
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
  };
  /**
   * An equality or disequality between two of our terms that holds in the
   * outer solver, waiting to be asserted.
   */
  struct OuterFact
  {
    TermId d_a;
    TermId d_b;
    bool d_pol;
  };
  /**
   * The sizes of everything this solver accumulates, so that it can go back
   * to an earlier state: when a scope is popped, and when a round ends in a
   * conflict.
   */
  struct Checkpoint
  {
    size_t d_egraph;
    size_t d_arith;
    size_t d_instances;
    size_t d_clauses;
    size_t d_atoms;
    size_t d_assign;
    size_t d_clauseHead;
    size_t d_outerFacts;
    size_t d_outerFactHead;
    size_t d_candidates;
    size_t d_candidateHead;
    size_t d_touched;
    size_t d_touchedHead;
    size_t d_exportHead;
  };
  /** The current state, as a checkpoint */
  Checkpoint mkCheckpoint() const;
  /** Go back to the state of the checkpoint c */
  void restoreTo(const Checkpoint& c);
  /**
   * Called before anything is changed. The first time this happens in a scope
   * of the trail, the state is saved, to be restored when the scope is popped.
   */
  void ensureScopeSaved();

  /** The index of the atom for the formula atom, creating it if needed */
  size_t getAtom(TNode atom);
  /** The literal for the formula lit, which may be a negation */
  LitId getLit(TNode lit);
  /** The formula of a literal */
  Node getLitNode(LitId l) const;
  /** The value of a literal */
  Value value(LitId l) const;
  /** Decompose a clause formula into literals */
  /**
   * Assert the formula f, which belongs to the given instance, by adding its
   * clauses. z3 internalizes the body of an instance in the same way
   * (context::internalize_instance).
   */
  void addFormula(TNode f, size_t instance);
  /**
   * The literal standing for the formula f, adding the defining clauses of the
   * Boolean connectives inside it. The formula itself is used as its own
   * definitional atom, so the encoding of a shared subformula is shared.
   */
  LitId encode(TNode f, size_t instance);
  /** The literal of f, assuming its connectives are already defined */
  LitId litFor(TNode f);
  /** Add the clauses defining the atom of the connective f */
  void defineAtom(TNode f, size_t instance);
  /** Does f stand for a Boolean connective that gets defining clauses? */
  static bool needsDefinition(TNode f);
  /** Add a clause, which belongs to the given instance */
  void addClause(const std::vector<LitId>& lits, size_t instance);
  /** Note that the atom watches the term t, to be revisited on merges */
  void addWatch(TermId t, size_t atom);

  //---------------------------------------- the link to the outer solver
  /** The anchor of the outer class r, or undefinedTerm */
  TermId getAnchor(ENode* r) const;
  /** Make t the anchor of the outer class r */
  void setAnchor(ENode* r, TermId t);
  /**
   * Our term t is in the outer class whose representative is r. Make it the
   * anchor of r, or if r has one, note that t is equal to it.
   */
  void linkToOuter(TermId t, ENode* r);
  /** Note an outer fact, to be asserted at the next round */
  void addOuterFact(TermId a, TermId b, bool pol);
  /** Take the current value of the inner atoms from the outer solver */
  bool syncOuter();
  /** Assert the outer facts that are pending */
  bool processOuterFacts();
  /**
   * For the classes merged since the last time, check whether two of the
   * outer classes they now contain are disequal in the outer solver.
   */
  bool checkTouchedClasses(bool& progress);
  /** Assign the literal for atom with the given polarity as an outer fact */
  bool assignOuter(TNode atom, bool pol);
  //------------------------------------ end the link to the outer solver

  /**
   * Assign l, with the given reason. Returns false if l was already false, in
   * which case the conflict explanation has been recorded.
   */
  bool assign(LitId l, ReasonKind kind, size_t clause, std::vector<LitId> exp);
  /** Tell the theory about a newly assigned literal */
  bool assertToTheory(LitId l);
  /**
   * Examine the clause c under the current assignment, assigning its last
   * unassigned literal or recording a conflict. Returns false on a conflict.
   */
  bool visitClause(size_t c);
  /** Propagate to a fixed point. Returns false on a conflict. */
  bool propagate();
  /** Assign the atoms that the congruence closure implies */
  bool theoryPropagate(bool& progress);
  /** The literals in our atoms for the explanation exp of the theory */
  void toLits(const std::vector<Node>& exp, std::vector<LitId>& lits) const;
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
  /** Export the propagations derived since the last round */
  void exportPropagations();
  /** The negation of the formula of a literal */
  static Node negate(TNode lit);

  /** The trail of the engine, used to retract instances on a pop */
  Trail& d_trail;
  /** The quantifiers state, used to read the outer assignment */
  QuantifiersState& d_qstate;
  /** The e-graph mirror, i.e. the outer equivalence classes */
  EGraph& d_mirror;
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
  /** For each term, the atoms to revisit when its class is merged */
  std::vector<std::vector<size_t>> d_watches;
  /** The clauses of the inner problem */
  std::vector<Clause> d_clauses;
  /** The clauses from d_clauseHead on have not been examined yet */
  size_t d_clauseHead;
  /** The assignment, in order */
  std::vector<Assignment> d_assignTrail;
  /** The literals whose consequences have not been processed yet */
  std::vector<LitId> d_queue;
  /** The explanation of the conflict of the current round */
  std::vector<LitId> d_conflictExp;
  /** The clause the conflict came from, if any */
  size_t d_conflictClause;
  /** The terms true and false of the congruence closure */
  TermId d_trueTerm;
  TermId d_falseTerm;
  /**
   * For each class of the mirror, identified by its representative, one of our
   * terms in it, if any.
   */
  std::unordered_map<ENode*, TermId> d_anchors;
  /** The outer facts, those from d_outerFactHead on not yet asserted */
  std::vector<OuterFact> d_outerFacts;
  size_t d_outerFactHead;
  /**
   * The atoms that a merge may have made implied, those from
   * d_candidateHead on not yet examined.
   */
  std::vector<size_t> d_candidates;
  size_t d_candidateHead;
  /**
   * The terms whose classes were merged into, those from d_touchedHead on not
   * yet checked against the outer disequalities.
   */
  std::vector<TermId> d_touched;
  size_t d_touchedHead;
  /** The assignments from d_exportHead on have not been considered for export
   */
  size_t d_exportHead;
  /**
   * The number of scopes of the trail at the last time the state was saved.
   * Restored by the trail, so that it tells whether the current scope has
   * been saved.
   */
  uint32_t d_savedScope;
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
