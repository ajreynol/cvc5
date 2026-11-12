/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The Boolean search of the eager E-matching core.
 *
 * Ported from Z3: the Boolean part of src/smt/smt_context.{h,cpp},
 * src/smt/smt_internalizer.cpp.
 * Z3 is Copyright (c) Microsoft Corporation and licensed under the MIT
 * License, see licenses/z3-LICENSE.
 *
 * In Z3 this is part of the context class; here it is separate so that the
 * Boolean search and the theory reasoning have an explicit boundary.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__PROP_CORE_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__PROP_CORE_H

#include <algorithm>
#include <memory>
#include <string>
#include <vector>

#include "context/cdlist.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "prop/sat_solver_types.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/eager/bool_var_data.h"
#include "theory/quantifiers/eager/clause.h"
#include "theory/quantifiers/eager/quantifier_normalizer.h"
#include "theory/quantifiers/eager/relevancy.h"
#include "theory/quantifiers/eager/statistics.h"
#include "theory/quantifiers/eager/trail.h"
#include "theory/quantifiers/eager/watch_list.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

class SmtContext;

/** The value of a literal: cvc5's SAT value, true, false or unknown. */
using prop::SAT_VALUE_FALSE;
using prop::SAT_VALUE_TRUE;
using prop::SAT_VALUE_UNKNOWN;
using prop::SatValue;

/**
 * The Boolean side of the core: the Boolean variables and their assignment,
 * the watch lists and the clauses of the Boolean structure, Boolean
 * constraint propagation and relevancy, by scope.
 *
 * It mirrors, for the theory side, the assignment of the atoms that cvc5
 * asserts: it never decides or resolves a conflict itself. Its clauses stay
 * private: the theory side sends cvc5 its instances and lemmas.
 *
 * SmtContext owns this object and drives it: the input, the propagation
 * fixpoint and the scopes are SmtContext's: this side's assignment and
 * clauses are context-dependent lists on its trail stack, popped with it,
 * after which SmtContext calls notifyPopped. This side notifies it of the
 * assigned atoms (enqueueAtom), the relevant terms (notifyRelevant) and the
 * deleted variables (notifyBoolVarDeleted).
 */
class PropCore : protected EnvObj
{
 public:
  /** Make the Boolean side of ctx, which counts its work in stats. */
  PropCore(Env& env, SmtContext& ctx, Statistics& stats);
  ~PropCore();

  PropCore(const PropCore&) = delete;
  PropCore& operator=(const PropCore&) = delete;

  /** Make the variable of t, the constant true, assigned by an axiom. */
  void initTrue(TNode t);

  // ------------------------------------------------------ Boolean variables
  /**
   * Make the Boolean variable of n, which has none, at the current scope.
   * Pushes a trail object that deletes it when the scope is popped.
   */
  SatVariable mkBoolVar(TNode n);

  /** Undo the last mkBoolVar; invoked from the trail. */
  void undoMkBoolVar();

  /** The Boolean variable of n; the id of n must be in the map. */
  SatVariable getBoolVar(TNode n) const { return d_expr2BoolVar[n.getId()]; }

  /** The Boolean variable of the expression with this id, unchecked. */
  SatVariable getBoolVarOfId(size_t id) const { return d_expr2BoolVar[id]; }

  /** The Boolean variable of the expression with this id, or undef. */
  SatVariable getBoolVarOfIdOption(size_t id) const
  {
    return id < d_expr2BoolVar.size() ? d_expr2BoolVar[id]
                                      : prop::undefSatVariable;
  }

  /** Map the expression with this id to v, growing the map as needed. */
  void setBoolVar(size_t id, SatVariable v)
  {
    if (id >= d_expr2BoolVar.size())
    {
      d_expr2BoolVar.resize(id + 1, prop::undefSatVariable);
    }
    d_expr2BoolVar[id] = v;
  }

  /** The expression of the Boolean variable v. */
  TNode boolVar2Expr(SatVariable v) const { return d_boolVar2Expr[v]; }

  /**
   * The literal of n, which is a Boolean constant, an internalized
   * expression or the negation of one.
   */
  SatLiteral getLiteral(TNode n) const;

  /** The number of Boolean variables that currently exist. */
  size_t getNumBoolVars() const { return d_bInternalizedStack.size(); }

  /** True if n has a Boolean variable. */
  bool bInternalized(TNode n) const
  {
    return getBoolVarOfIdOption(n.getId()) != prop::undefSatVariable;
  }

  /**
   * True if getLiteral can map the literal n: it is false, or it, or the
   * argument of its negation, has a Boolean variable.
   */
  bool litInternalized(TNode n) const
  {
    if (n.isConst() && !n.getConst<bool>())
    {
      return true;
    }
    return n.getKind() == Kind::NOT ? bInternalized(n[0]) : bInternalized(n);
  }

  /** The data of the Boolean variable v. */
  BoolVarData& getBdata(SatVariable v) { return d_bdata[v]; }

  /** The data of the Boolean variable v, read-only. */
  const BoolVarData& getBdata(SatVariable v) const { return d_bdata[v]; }

  /** The scope level at which v was internalized. */
  uint32_t getInternLevel(SatVariable v) const
  {
    return getBdata(v).getInternLevel();
  }

  // ------------------------------------------------------------- assignment
  /** The value of the literal with index litIdx (SatLiteral::toInt). */
  SatValue getLitAssignment(size_t litIdx) const
  {
    return d_assignment[litIdx];
  }

  /** The value of the literal l. */
  SatValue getAssignment(SatLiteral l) const
  {
    return getLitAssignment(l.toInt());
  }

  /** The value of the Boolean variable v. */
  SatValue getAssignment(SatVariable v) const
  {
    return getAssignment(SatLiteral(v));
  }

  /**
   * The value of n, which is false, an internalized expression or the
   * negation of one.
   */
  SatValue getAssignment(TNode n) const;

  /** Like getAssignment, but returns SAT_VALUE_UNKNOWN if n is not
   * internalized. */
  SatValue findAssignment(TNode n) const;

  /**
   * Assign l true: a conflict if l is false, nothing if it is already true.
   */
  void assign(SatLiteral l)
  {
    Assert(l != s_falseLiteral);
    Assert(l != prop::undefSatLiteral);
    switch (getAssignment(l))
    {
      case SAT_VALUE_FALSE: setConflict(); break;
      case SAT_VALUE_UNKNOWN: assignCore(l); break;
      case SAT_VALUE_TRUE: return;
    }
  }

  /**
   * Assign the unassigned l true, and enqueue it for the theory side if it
   * is a relevant atom.
   */
  void assignCore(SatLiteral l);

  /** Boolean constraint propagation; returns false on a conflict. */
  bool bcp();

  /** The next assigned literal for bcp to propagate. */
  size_t getQhead() const { return d_qhead; }

  /** Have bcp propagate the assigned literals from qhead on again. */
  void setQhead(size_t qhead) { d_qhead = qhead; }

  /**
   * Propagate relevancy, for the literals assigned from qhead on, which bcp
   * propagated.
   */
  void propagateRelevancy(size_t qhead);

  // -------------------------------------------------------------- conflicts
  /** Record a conflict at the current scope, which the pop clears. */
  void setConflict() { d_conflict = true; }

  /** True if there is a conflict, at this scope or by an asserted formula. */
  bool inconsistent() const { return d_conflict || d_assertedInconsistent; }

  /**
   * An asserted formula is false, which no backtracking undoes, only the pop
   * of the user scope it was asserted in.
   */
  void setAssertedInconsistent() { d_assertedInconsistent = true; }

  /** True if an asserted formula is false, see setAssertedInconsistent. */
  bool isAssertedInconsistent() const { return d_assertedInconsistent; }

  // -------------------------------------------------------------- relevancy
  //
  // Relevancy runs at level 2: an assigned atom other than a quantifier
  // reaches the theory side only once it is relevant.

  /** True if n is marked relevant. */
  bool isRelevant(TNode n) const
  {
    return d_relevancyPropagator->isRelevant(n);
  }

  /** True if the expression of v is marked relevant. */
  bool isRelevant(SatVariable v) const { return isRelevant(boolVar2Expr(v)); }

  /** True if the variable of l, which is not a constant, is relevant. */
  bool isRelevant(SatLiteral l) const
  {
    Assert(l != s_trueLiteral && l != s_falseLiteral);
    return isRelevant(l.getSatVariable());
  }

  /** Mark n and its class relevant, and propagate relevancy. */
  void markAsRelevant(TNode n)
  {
    d_relevancyPropagator->markAsRelevant(n);
    d_relevancyPropagator->propagate();
  }

  /** Mark the expression of v relevant, and propagate relevancy. */
  void markAsRelevant(SatVariable v) { markAsRelevant(boolVar2Expr(v)); }

  /** Mark the variable of l relevant, and propagate relevancy. */
  void markAsRelevant(SatLiteral l) { markAsRelevant(l.getSatVariable()); }

  /** Mark target relevant whenever source is, until the scope is popped. */
  void addRelevancyDependency(TNode source, TNode target)
  {
    d_relevancyPropagator->addDependency(source, target);
  }

  /**
   * Apply the relevancy rule of the gate n again, if it is relevant, when l
   * is assigned true.
   */
  void addGateWatch(SatLiteral l, TNode gate)
  {
    d_relevancyPropagator->addGateWatch(
        boolVar2Expr(l.getSatVariable()), !l.isNegated(), gate);
  }

  /** The classes of n1 and n2 merge, see RelevancyPropagator::notifyMerge. */
  void notifyRelevancyMerge(TNode n1, TNode n2)
  {
    d_relevancyPropagator->notifyMerge(n1, n2);
  }

  /**
   * The event handler invoked by the relevancy propagator when n becomes
   * relevant. This side requeues an assigned atom that now reaches the theory
   * side; then the theory side is notified.
   */
  void notifyRelevant(TNode n);

  /** Destroy the relevancy propagator, when the context is flushed. */
  void flushRelevancy() { d_relevancyPropagator.reset(nullptr); }

  // -------------------------------------------------- the Boolean structure
  //
  // The clauses that encode the Boolean structure of the input, as cvc5's
  // CnfStream does. The theory side's internalizer walks the input and calls
  // these where a gate or a root assertion occurs.

  /**
   * Make an auxiliary clause, of a gate or a root assertion, which is deleted
   * on backtracking.
   */
  void mkClause(size_t numLits, SatLiteral* lits);
  void mkClause(SatLiteral l1, SatLiteral l2);
  void mkClause(SatLiteral l1, SatLiteral l2, SatLiteral l3);
  /**
   * Add the clauses that define the Boolean variable of the gate n in terms
   * of its arguments, and the relevancy watches of n. Called once, when the
   * variable of n is made.
   */
  void mkGateConstraints(TNode n);
  /** Have the and-gate n watch each of its arguments for false. */
  void addAndRelWatches(TNode n);
  /** Have the or-gate n watch each of its arguments for true. */
  void addOrRelWatches(TNode n);
  /** Have the implication n watch its antecedent false, consequent true. */
  void addImpliesRelWatches(TNode n);
  /** Have the ite n watch its condition for either value. */
  void addIteRelWatches(TNode n);

  // ------------------------------------------------------------ host mode
  /**
   * Assign l, which the host asserted. Returns false if l is false here, a
   * conflict.
   */
  bool hostAssign(SatLiteral l);

  // ----------------------------------------------------------------- scopes
  /**
   * The scopes are those of the trail stack: popping one unassigns the
   * variables assigned in it and retires the clauses made in it.
   */
  uint32_t getScopeLevel() const;

  /**
   * Delete the clauses retired by the scopes just popped, or by all scopes
   * when the trail stack was reset.
   */
  void notifyPopped();

  /** Whether this side has propagation work pending. */
  bool hasPendingPropagation() const;

 private:
  /** Unassigns a literal popped from d_assignedLiterals. */
  struct UnassignCleanup
  {
    /** The owner of the list. */
    PropCore* d_core;
    /** Unassign l. */
    void operator()(SatLiteral& l) { d_core->unassign(l); }
  };
  /** Retires a clause popped from d_auxClauses. */
  struct RetireCleanup
  {
    /** The owner of the list. */
    PropCore* d_core;
    /** Add c to the clauses to delete in notifyPopped. */
    void operator()(Clause*& c) { d_core->d_retiredClauses.push_back(c); }
  };

  /** The trail object that undoes mkBoolVar. */
  class MkBoolVarTrail : public Trail
  {
   public:
    /** A trail object that undoes the mkBoolVar calls of core. */
    MkBoolVarTrail(PropCore& core) : d_core(core) {}
    /** Delete the last Boolean variable made. */
    void undo() override { d_core.undoMkBoolVar(); }

   private:
    /** The core whose variable is deleted. */
    PropCore& d_core;
  };

  /** Make l and its negation unassigned. */
  void unassign(SatLiteral l);

  // the Boolean structure
  /** The clauses defining the variable of the negation n. */
  void mkNotCnstr(TNode n);
  /** The clauses defining the variable of the conjunction n. */
  void mkAndCnstr(TNode n);
  /** The clauses defining the variable of the disjunction n. */
  void mkOrCnstr(TNode n);
  /** The clauses defining the variable of the implication n. */
  void mkImpliesCnstr(TNode n);
  /** The clauses defining the variable of n, an iff, or an xor if sign. */
  void mkIffCnstr(TNode n, bool sign);
  /** The clauses defining the variable of the Boolean ite n. */
  void mkIteCnstr(TNode n);

  // clause management
  /** Remove cls from the watch list of its literal at idx (0 or 1). */
  void removeWatchLiteral(Clause* cls, size_t idx);
  /** Unwatch and delete cls, which is not marked deleted. */
  void delClause(Clause* cls);
  /**
   * Sort the literals of an auxiliary clause and remove the false and
   * duplicate ones, in place, updating numLits. Returns false if the clause
   * is equivalent to true.
   */
  bool simplifyAuxClauseLiterals(size_t& numLits, SatLiteral* lits);
  /**
   * True if the clause l1 or l2 can be kept only in the watch lists: it is
   * made at the base level, over variables of the base level.
   */
  bool useBinaryClauseOpt(SatLiteral l1, SatLiteral l2) const;
  /** Add cls to the watch list of its literal at idx (0 or 1). */
  void addWatchLiteral(Clause* cls, size_t idx);

  /** The theory side. */
  SmtContext& d_ctx;
  /** The statistics of the core. */
  Statistics& d_stats;

  /** The relevancy propagator, destroyed by flushRelevancy. */
  std::unique_ptr<RelevancyPropagator> d_relevancyPropagator;

  /** Maps the id of an expression to its Boolean variable. */
  std::vector<SatVariable> d_expr2BoolVar;
  /** Maps a Boolean variable to its expression. */
  std::vector<Node> d_boolVar2Expr;
  /** The Boolean expressions already internalized. */
  std::vector<Node> d_bInternalizedStack;
  /** Maps a literal index to its assignment. */
  std::vector<SatValue> d_assignment;
  /** The watch list of each literal. */
  std::vector<WatchList> d_watches;
  /** The data of each Boolean variable. */
  std::vector<BoolVarData> d_bdata;
  /**
   * The clauses of the popped scopes, which are deleted together after the
   * pop, so that a large batch sweeps the watch lists once.
   */
  ClauseVector d_retiredClauses;
  /** The transient clauses, made at scopes above the base level. */
  context::CDList<Clause*, RetireCleanup> d_auxClauses;
  /** The assigned literals, in order, unassigned when popped. */
  context::CDList<SatLiteral, UnassignCleanup> d_assignedLiterals;
  /** The index in d_assignedLiterals of the next literal for bcp. */
  size_t d_qhead;

  /** True if a conflict was found at the current scope. */
  bool d_conflict;
  /** True if a formula asserted false. */
  context::CDO<bool> d_assertedInconsistent;

  /** The trail object pushed by every mkBoolVar, through pushPtr. */
  MkBoolVarTrail d_mkBoolVarTrail;
};

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER__PROP_CORE_H */
