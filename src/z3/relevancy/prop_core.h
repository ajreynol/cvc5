/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The Boolean search of the ported Z3 core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), the
 * Boolean part of files src/smt/smt_context.{h,cpp} and
 * src/smt/smt_internalizer.cpp, and recast in cvc5 style. In Z3 this is part
 * of the context class; here it is separate so that the Boolean search and
 * the theory reasoning have an explicit boundary.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__RELEVANCY__PROP_CORE_H
#define CVC5__Z3__RELEVANCY__PROP_CORE_H

#include <algorithm>
#include <memory>
#include <string>
#include <vector>

#include "expr/node.h"
#include "prop/sat_solver_types.h"
#include "smt/env_obj.h"
#include "z3/relevancy/bool_var_data.h"
#include "z3/relevancy/clause.h"
#include "z3/relevancy/relevancy.h"
#include "z3/relevancy/watch_list.h"
#include "z3/util/ast.h"
#include "z3/util/literal.h"
#include "z3/util/statistics.h"
#include "z3/util/trail.h"

namespace cvc5::internal {
namespace z3 {

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
 * fixpoint and the scopes are SmtContext's, which pushes and pops this
 * side's scopes with its own. This side notifies it of the assigned atoms
 * (enqueueAtom), the relevant terms (notifyRelevant) and the deleted
 * variables (notifyBoolVarDeleted).
 */
class PropCore : protected EnvObj
{
 public:
  PropCore(Env& env, SmtContext& ctx, Statistics& stats);
  ~PropCore();

  PropCore(const PropCore&) = delete;
  PropCore& operator=(const PropCore&) = delete;

  /** Make the variable of t, the constant true, assigned by an axiom. */
  void initTrue(TNode t);
  /** Delete all clauses, when the context is flushed. */
  void flushClauses();

  // ------------------------------------------------------ Boolean variables
  BoolVar mkBoolVar(TNode n);

  /** Undo the last mkBoolVar; invoked from the trail. */
  void undoMkBoolVar();

  BoolVar getBoolVar(TNode n) const { return d_expr2BoolVar[n.getId()]; }

  BoolVar getBoolVarOfId(size_t id) const { return d_expr2BoolVar[id]; }

  BoolVar getBoolVarOfIdOption(size_t id) const
  {
    return id < d_expr2BoolVar.size() ? d_expr2BoolVar[id] : s_nullBoolVar;
  }

  void setBoolVar(size_t id, BoolVar v)
  {
    if (id >= d_expr2BoolVar.size())
    {
      d_expr2BoolVar.resize(id + 1, s_nullBoolVar);
    }
    d_expr2BoolVar[id] = v;
  }

  TNode boolVar2Expr(BoolVar v) const { return d_boolVar2Expr[v]; }

  Literal getLiteral(TNode n) const;

  size_t getNumBoolVars() const { return d_bInternalizedStack.size(); }

  bool bInternalized(TNode n) const
  {
    return getBoolVarOfIdOption(n.getId()) != s_nullBoolVar;
  }

  bool litInternalized(TNode n) const
  {
    if (n.isConst() && !n.getConst<bool>())
    {
      return true;
    }
    return n.getKind() == Kind::NOT ? bInternalized(n[0]) : bInternalized(n);
  }

  BoolVarData& getBdata(BoolVar v) { return d_bdata[v]; }

  const BoolVarData& getBdata(BoolVar v) const { return d_bdata[v]; }

  /** The scope level at which v was internalized. */
  uint32_t getInternLevel(BoolVar v) const
  {
    return getBdata(v).getInternLevel();
  }

  // ------------------------------------------------------------- assignment
  SatValue getLitAssignment(size_t litIdx) const
  {
    return d_assignment[litIdx];
  }

  SatValue getAssignment(Literal l) const
  {
    return getLitAssignment(l.index());
  }

  SatValue getAssignment(BoolVar v) const { return getAssignment(Literal(v)); }

  SatValue getAssignment(TNode n) const;

  /** Like getAssignment, but returns SAT_VALUE_UNKNOWN if n is not
   * internalized. */
  SatValue findAssignment(TNode n) const;

  void assign(Literal l)
  {
    Assert(l != s_falseLiteral);
    Assert(l != s_nullLiteral);
    switch (getAssignment(l))
    {
      case SAT_VALUE_FALSE: setConflict(); break;
      case SAT_VALUE_UNKNOWN: assignCore(l); break;
      case SAT_VALUE_TRUE: return;
    }
  }

  void assignCore(Literal l);

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
  void setConflict() { d_conflict = true; }

  bool inconsistent() const { return d_conflict || d_assertedInconsistent; }

  /** An asserted formula is false, which no backtracking undoes. */
  void setAssertedInconsistent() { d_assertedInconsistent = true; }

  bool isAssertedInconsistent() const { return d_assertedInconsistent; }

  // -------------------------------------------------------------- relevancy
  //
  // Relevancy runs at level 2: an assigned atom other than a quantifier
  // reaches the theory side only once it is relevant.

  bool isRelevant(TNode n) const
  {
    return d_relevancyPropagator->isRelevant(n);
  }

  bool isRelevant(BoolVar v) const { return isRelevant(boolVar2Expr(v)); }

  bool isRelevant(Literal l) const
  {
    Assert(l != s_trueLiteral && l != s_falseLiteral);
    return isRelevant(l.var());
  }

  void markAsRelevant(TNode n)
  {
    d_relevancyPropagator->markAsRelevant(n);
    d_relevancyPropagator->propagate();
  }

  void markAsRelevant(BoolVar v) { markAsRelevant(boolVar2Expr(v)); }

  void markAsRelevant(Literal l) { markAsRelevant(l.var()); }

  void addRelevancyDependency(TNode source, TNode target)
  {
    d_relevancyPropagator->addDependency(source, target);
  }

  void addRelWatch(Literal l, RelevancyHandler* eh)
  {
    d_relevancyPropagator->addWatch(boolVar2Expr(l.var()), !l.sign(), eh);
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

  /** Make a clause of a root assertion. */
  void mkRootClause(size_t numLits, Literal* lits);
  void mkRootClause(Literal l1, Literal l2);
  /** The relevancy watches of the gate n, asserted as a root. */
  void addAndRelWatches(TNode n);
  void addOrRelWatches(TNode n);
  void addImpliesRelWatches(TNode n);
  void addIteRelWatches(TNode n);

  // ------------------------------------------------------------ host mode
  /**
   * Assign l, which the host asserted. Returns false if l is false here, a
   * conflict.
   */
  bool hostAssign(Literal l);
  /**
   * Move to out the expressions of the variables that became relevant while
   * unassigned since the last call.
   */
  void hostTakeRelevant(std::vector<Node>& out)
  {
    out.insert(out.end(), d_hostRelevant.begin(), d_hostRelevant.end());
    d_hostRelevant.clear();
  }
  /**
   * Add the clauses that define the Boolean variable of the gate n in terms
   * of its arguments, and the relevancy watches of n. Called once, when the
   * variable of n is made.
   */
  void mkGateConstraints(TNode n);

  void mkGateClause(size_t numLits, Literal* lits);
  void mkGateClause(Literal l1, Literal l2);
  void mkGateClause(Literal l1, Literal l2, Literal l3);

  // ---------------------------------------------------------------- clauses
  /** Make an auxiliary clause, which is deleted on backtracking. */
  Clause* mkClause(size_t numLits, Literal* lits);

  // ----------------------------------------------------------------- scopes
  uint32_t getScopeLevel() const
  {
    return static_cast<uint32_t>(d_scopes.size());
  }

  /** Open a new scope. */
  void pushScope();

  /**
   * Backtrack numScopes scopes: delete the clauses and unassign the
   * variables of the scopes popped.
   */
  void popScope(size_t numScopes);

  /** Whether this side has propagation work pending. */
  bool hasPendingPropagation() const;

 private:
  struct Scope
  {
    size_t d_assignedLiteralsLim;
    size_t d_auxClausesLim;
  };

  /** The trail object that undoes mkBoolVar. */
  class MkBoolVarTrail : public Trail
  {
   public:
    MkBoolVarTrail(PropCore& core) : d_core(core) {}
    void undo() override { d_core.undoMkBoolVar(); }

   private:
    PropCore& d_core;
  };

  void unassignVars(size_t oldLim);

  // the Boolean structure
  void mkNotCnstr(TNode n);
  void mkAndCnstr(TNode n);
  void mkOrCnstr(TNode n);
  void mkImpliesCnstr(TNode n);
  void mkIffCnstr(TNode n, bool sign);
  void mkIteCnstr(TNode n);

  // clause management
  void removeWatchLiteral(Clause* cls, size_t idx);
  void delClause(Clause* cls);
  void delClauses(ClauseVector& v, size_t oldSize);
  bool simplifyAuxClauseLiterals(size_t& numLits, Literal* lits);
  bool useBinaryClauseOpt(Literal l1, Literal l2) const;
  void addWatchLiteral(Clause* cls, size_t idx);

  /** The unassigned variables that became relevant; see hostTakeRelevant. */
  std::vector<Node> d_hostRelevant;

  /** The theory side. */
  SmtContext& d_ctx;
  Statistics& d_stats;

  std::unique_ptr<RelevancyPropagator> d_relevancyPropagator;

  /** Maps the id of an expression to its Boolean variable. */
  std::vector<BoolVar> d_expr2BoolVar;
  /** Maps a Boolean variable to its expression. */
  std::vector<Node> d_boolVar2Expr;
  /** The Boolean expressions already internalized. */
  std::vector<Node> d_bInternalizedStack;
  /** Maps a literal index to its assignment. */
  std::vector<SatValue> d_assignment;
  /** The watch list of each literal. */
  std::vector<WatchList> d_watches;
  std::vector<BoolVarData> d_bdata;
  ClauseVector d_auxClauses;
  LiteralVector d_assignedLiterals;
  size_t d_qhead;

  /** True if a conflict was found at the current scope. */
  bool d_conflict;
  /** True if a formula asserted false. */
  bool d_assertedInconsistent;

  std::vector<Scope> d_scopes;

  MkBoolVarTrail d_mkBoolVarTrail;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__RELEVANCY__PROP_CORE_H */
