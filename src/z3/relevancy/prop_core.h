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
#include "smt/env_obj.h"
#include "z3/relevancy/bool_var_data.h"
#include "z3/relevancy/clause.h"
#include "z3/relevancy/relevancy.h"
#include "z3/relevancy/theory_side.h"
#include "z3/relevancy/watch_list.h"
#include "z3/util/ast.h"
#include "z3/util/literal.h"
#include "z3/util/statistics.h"
#include "z3/util/trail.h"
#include "z3/util/types.h"

namespace cvc5::internal {
namespace z3 {

/**
 * The Boolean side of the core: the Boolean variables and their assignment,
 * the watch lists and the clauses of the Boolean structure, Boolean
 * constraint propagation, relevancy, the scope levels, and the propagation
 * fixpoint.
 *
 * It runs in host mode: cvc5's prop engine searches, and this class mirrors,
 * for the theory side, the assignment of the atoms that cvc5 asserts. It
 * never decides or resolves a conflict itself, and its scopes follow cvc5's
 * SAT context (see HostCore). Its clauses stay private: the theory side
 * sends cvc5 its instances and lemmas (SmtContext::setLemmaSender).
 *
 * The theory side, SmtContext, owns this object. This side calls it, through
 * the TheorySide interface,
 * theoryPropagate and hasPendingTheoryWork for the propagation fixpoint,
 * finalCheck, initSearchEh, and pushTheoryScope, popTheoryScopeBegin and
 * popTheoryScopeEnd when scopes are pushed and popped; besides that, it
 * hands it the assigned atoms (enqueueAtom), notifies it of relevant terms
 * (relevantEh), and has it internalize the asserted formulas.
 */
class PropCore : protected EnvObj
{
 public:
  /** A unit literal that is reasserted after every backtrack. */
  struct ReplayUnit
  {
    Node d_unit;
    bool d_sign;
    bool d_relevant;
  };

  PropCore(Env& env, TheorySide& ctx, Statistics& stats);
  ~PropCore();

  PropCore(const PropCore&) = delete;
  PropCore& operator=(const PropCore&) = delete;

  /** Make the variable of t, the constant true, assigned by an axiom. */
  void initTrue(TNode t);
  /** Delete all clauses, when the context is flushed. */
  void flushClauses();

  // ------------------------------------------------------------------- input
  /** Assert a (prepared) formula. */
  void assertFormula(TNode e);

  /** Add e to the asserted formulas, splitting a top-level conjunction. */
  void pushAssertion(TNode e);

  /**
   * Internalize the asserted formulas that have not been internalized yet,
   * through the theory side's SmtContext::internalizeAssertion.
   */
  void internalizeAssertions();

  size_t getNumAssertedFormulas() const { return d_assertedFormulas.size(); }

  TNode getAssertedFormula(size_t idx) const { return d_assertedFormulas[idx]; }

  /** True if the input contains quantifiers. */
  bool hasQuantifiers() const { return d_hasQuantifiers; }

  // ------------------------------------------------------ Boolean variables
  BoolVar mkBoolVar(TNode n);

  /** Undo the last mkBoolVar; invoked from the trail. */
  void undoMkBoolVar();

  BoolVar getBoolVar(TNode n) const { return d_expr2BoolVar[n.getId()]; }

  BoolVar getBoolVarOfId(size_t id) const { return d_expr2BoolVar[id]; }

  BoolVar getBoolVarOfIdOption(size_t id) const
  {
    return getx(d_expr2BoolVar, id, s_nullBoolVar);
  }

  void setBoolVar(size_t id, BoolVar v)
  {
    setx(d_expr2BoolVar, id, v, s_nullBoolVar);
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
  LBool getLitAssignment(size_t litIdx) const
  {
    return static_cast<LBool>(d_assignment[litIdx]);
  }

  LBool getAssignment(Literal l) const { return getLitAssignment(l.index()); }

  LBool getAssignment(BoolVar v) const { return getAssignment(Literal(v)); }

  LBool getAssignment(TNode n) const;

  /** Like getAssignment, but returns L_UNDEF if n is not internalized. */
  LBool findAssignment(TNode n) const;

  void assign(Literal l)
  {
    Assert(l != s_falseLiteral);
    Assert(l != s_nullLiteral);
    switch (getAssignment(l))
    {
      case L_FALSE: setConflict(); break;
      case L_UNDEF: assignCore(l); break;
      case L_TRUE: return;
    }
  }

  void assignCore(Literal l);

  /** Boolean constraint propagation; returns false on a conflict. */
  bool bcp();

  // -------------------------------------------------------------- conflicts
  void setConflict() { d_conflict = true; }

  bool inconsistent() const { return d_conflict || d_assertedInconsistent; }

  // -------------------------------------------------------------- relevancy
  //
  // Relevancy runs at level 2: an assigned atom other than a quantifier
  // reaches the theory side only once it is relevant.

  bool isRelevantCore(TNode n) const
  {
    return d_relevancyPropagator->isRelevant(n);
  }

  bool isRelevant(TNode n) const { return isRelevantCore(n); }

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

  void addRelWatch(Literal l, RelevancyEh* eh)
  {
    d_relevancyPropagator->addWatch(boolVar2Expr(l.var()), !l.sign(), eh);
  }

  /**
   * The event handler invoked by the relevancy propagator when n becomes
   * relevant. This side requeues an assigned atom that now reaches the theory
   * side; then the theory side is notified.
   */
  void relevantEh(TNode n);

  /** Destroy the relevancy propagator, when the context is flushed. */
  void flushRelevancy() { d_relevancyPropagator.reset(nullptr); }

  // -------------------------------------------------- the Boolean structure
  //
  // The clauses that encode the Boolean structure of the input, as cvc5's
  // CnfStream does. The theory side's internalizer walks the input and calls
  // these where a gate or a root assertion occurs.

  /**
   * Assert the root formula n, after the theory side has internalized its
   * subterms (SmtContext::internalizeAssertion): the clauses of a root gate
   * over the literals of its arguments, which the theory side internalizes
   * here in turn, or the unit literal of anything else.
   */
  void assertRoot(TNode n);

  // ------------------------------------------------------------ host mode
  /**
   * Prepare the search: configure the theory side, internalize the asserted
   * formulas and start the search.
   */
  void hostInit();
  /** Push or pop scopes until the scope level is lvl. */
  void hostSyncLevel(uint32_t lvl);
  /**
   * The literal of n, an atom or a negated atom, internalizing the atom if
   * it is not internalized, for instance because it was deleted on
   * backtracking.
   */
  Literal hostLiteral(TNode n);
  /**
   * Assign l, which the host asserted. Returns false if l is false here, a
   * conflict.
   */
  bool hostAssign(Literal l);
  /** Propagate to a fixpoint; returns false on a conflict. */
  bool hostPropagate() { return propagate(); }
  /**
   * Move to out the expressions of the variables that became relevant while
   * unassigned since the last call.
   */
  void hostTakeRelevant(std::vector<Node>& out)
  {
    out.insert(out.end(), d_hostRelevant.begin(), d_hostRelevant.end());
    d_hostRelevant.clear();
  }
  /** Run the theory side's final check. */
  FinalCheckStatus hostFinalCheck();

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

  void addUnitToReassert(TNode unit, bool sign, bool relevant)
  {
    d_unitsToReassert.push_back(ReplayUnit{unit, sign, relevant});
  }

  // ----------------------------------------------------------------- scopes
  uint32_t getScopeLevel() const { return d_scopeLvl; }

  bool atBaseLevel() const { return d_scopeLvl == 0; }

  /** Open a new scope, on both sides. */
  void pushScope();

  /** Backtrack numScopes scopes, on both sides. */
  void popScope(size_t numScopes);

  /** Backtrack to the base level. */
  void popToBaseLvl();

  /** Propagate to a fixpoint; returns false on a conflict. */
  bool propagate();

  /** Whether either side has propagation work pending. */
  bool canPropagate() const;

  /** True if the resource limits were exceeded. */
  bool getCancelFlag();

  /**
   * True if the resource limits were exceeded during this search, which
   * then stays out of resources.
   */
  bool resourceLimitsExceeded();

 private:
  struct Scope
  {
    size_t d_assignedLiteralsLim;
    size_t d_auxClausesLim;
    size_t d_unitsToReassertLim;
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
  void assertDefault(TNode n);
  void mkRootClause(size_t numLits, Literal* lits);
  void mkRootClause(Literal l1, Literal l2);
  void addAndRelWatches(TNode n);
  void addOrRelWatches(TNode n);
  void addImpliesRelWatches(TNode n);
  void addIteRelWatches(TNode n);
  void mkNotCnstr(TNode n);
  void mkAndCnstr(TNode n);
  void mkOrCnstr(TNode n);
  void mkImpliesCnstr(TNode n);
  void mkIffCnstr(TNode n, bool sign);
  void mkIteCnstr(TNode n);

  void propagateRelevancy(size_t qhead);

  /**
   * Cache the generations of the atoms of the units that will be reasserted
   * when backtracking to newScopeLvl.
   */
  void cacheGeneration(uint32_t newScopeLvl);
  void reassertUnits(size_t unitsToReassertLim);

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
  TheorySide& d_ctx;
  Statistics& d_stats;

  std::unique_ptr<RelevancyPropagator> d_relevancyPropagator;

  /** Maps the id of an expression to its Boolean variable. */
  std::vector<BoolVar> d_expr2BoolVar;
  /** Maps a Boolean variable to its expression. */
  std::vector<Node> d_boolVar2Expr;
  /** The Boolean expressions already internalized. */
  std::vector<Node> d_bInternalizedStack;
  /** Maps a literal index to its assignment. */
  std::vector<int8_t> d_assignment;
  /** The watch list of each literal. */
  std::vector<WatchList> d_watches;
  std::vector<BoolVarData> d_bdata;
  ClauseVector d_auxClauses;
  std::vector<ReplayUnit> d_unitsToReassert;
  LiteralVector d_assignedLiterals;
  size_t d_qhead;

  /** True if a conflict was found at the current scope. */
  bool d_conflict;
  /** True if a formula asserted false. */
  bool d_assertedInconsistent;
  /** Set while the clauses are deleted on flushing. */
  bool d_flushing;

  /** The formulas asserted to the core, and how far they are internalized. */
  std::vector<Node> d_assertedFormulas;
  size_t d_assertedFormulasQhead;
  bool d_hasQuantifiers;
  bool d_internalizingAssertions;

  /** Whether the search started (hostInit). */
  bool d_searching;
  /** Whether the resource limits were exceeded during this search. */
  bool d_resourceOut;

  uint32_t d_scopeLvl;
  std::vector<Scope> d_scopes;

  MkBoolVarTrail d_mkBoolVarTrail;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__RELEVANCY__PROP_CORE_H */
