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

#ifndef CVC5__Z3__PROP_CORE_H
#define CVC5__Z3__PROP_CORE_H

#include <algorithm>
#include <memory>
#include <string>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "z3/ast.h"
#include "z3/b_justification.h"
#include "z3/bool_var_data.h"
#include "z3/case_split_queue.h"
#include "z3/clause.h"
#include "z3/justification.h"
#include "z3/params.h"
#include "z3/relevancy.h"
#include "z3/statistics.h"
#include "z3/types.h"
#include "z3/util/literal.h"
#include "z3/util/trail.h"
#include "z3/util/util.h"
#include "z3/watch_list.h"

namespace cvc5::internal {
namespace z3 {

class ConflictResolution;
class SmtContext;

/** The reason for an "unknown" result from check(). */
enum Failure
{
  OK,
  UNKNOWN,
  MEMOUT,
  /** the external cancel flag was set */
  CANCELED,
  /** the maximum number of conflicts was reached */
  NUM_CONFLICTS,
  /** a theory is incomplete */
  THEORY,
  RESOURCE_LIMIT,
  /** the logical context contains universal quantifiers */
  QUANTIFIERS
};

std::ostream& operator<<(std::ostream& out, Failure f);

/**
 * The Boolean search of the core: the Boolean variables and their
 * assignment, the watch lists and the clauses, Boolean constraint
 * propagation, the variable activity and phase heuristics, the case split
 * queue, the scope levels, conflict resolution, relevancy, and the search
 * driver (search, restarts, decisions, the propagation fixpoint and
 * backtracking).
 *
 * This is the propositional side of the boundary described in
 * PROP_THEORY_SPLIT.md. The theory side, SmtContext, owns this object. The
 * driver calls the theory side through its scheduling and backtracking
 * contract: theoryPropagate and hasPendingTheoryWork for the propagation
 * fixpoint, finalCheck when every variable is assigned, initSearchEh,
 * restartEh and checkModel around the search, notifyConflictResolved after
 * each conflict, clearPropagationQueues when a conflict is found, and
 * pushTheoryScope, popTheoryScopeBegin and popTheoryScopeEnd when scopes are
 * pushed and popped. Besides that, what this side asks of the theory side
 * goes through the SmtContext reference d_ctx and is limited to:
 *  - handing assigned atoms to the theory side (enqueueAtom);
 *  - notifying it that a term became relevant (relevantEh), after this side
 *    has handled the notification; and the members of an equivalence class,
 *    which share their relevancy, for the relevancy propagator (findENode);
 *  - configuring the core and internalizing the asserted formulas
 *    (setupContext, internalizeAssertion, and internalizeRec for the
 *    arguments of a root assertion), recreating the atoms of clauses that
 *    survive backtracking (internalize), and caching the generations the
 *    latter had (cacheGeneration);
 *  - at the end of a check, whether a satisfying assignment is a model
 *    (canConfirmModel) and the quantifier profile (reportQuantifierProfile);
 *  - removing a deleted quantifier variable (notifyBoolVarDeleted);
 *  - the phase hint of a theory (getTheory);
 *  - the infrastructure the two sides share: the trail, the region-allocated
 *    justifications and the random number generator.
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

  PropCore(Env& env, SmtContext& ctx, Params& params, Statistics& stats);
  ~PropCore();

  PropCore(const PropCore&) = delete;
  PropCore& operator=(const PropCore&) = delete;

  /**
   * Make the conflict resolution and the case split queue, which the theory
   * side's constructor calls.
   */
  void finishInit();
  /** Make the variable of t, the constant true, assigned by an axiom. */
  void initTrue(TNode t);
  /** Delete all clauses, when the context is flushed. */
  void flushClauses();

  // --------------------------------------------- input and the entry points
  //
  // These are what Z3PropEngine drives: the formulas asserted to the core,
  // the checks and the user scopes.

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

  const std::vector<Node>& getAssertedFormulas() const
  {
    return d_assertedFormulas;
  }

  /** True if the input contains quantifiers. */
  bool hasQuantifiers() const { return d_hasQuantifiers; }

  /** Run the search over the asserted formulas. */
  LBool check();

  /** Configure the core and then run the search. */
  LBool setupAndCheck();

  /** Push a user scope. */
  void push();

  /** Pop numScopes user scopes. */
  void pop(size_t numScopes);

  /** Why the last search answered L_UNDEF. */
  const std::string& getReasonUnknown() const { return d_unknown; }

  void setReasonUnknown(const std::string& msg) { d_unknown = msg; }

  // ------------------------------------------------------ Boolean variables
  BoolVar mkBoolVar(TNode n);

  /** Undo the last mkBoolVar; invoked from the trail. */
  void undoMkBoolVar();

  void resetBoolVars() { d_expr2BoolVar.clear(); }

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

  Node literal2Expr(Literal l) const;

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

  size_t getNumBInternalized() const { return d_bInternalizedStack.size(); }

  TNode getBInternalized(size_t idx) const { return d_bInternalizedStack[idx]; }

  BoolVarData& getBdata(BoolVar v) { return d_bdata[v]; }

  const BoolVarData& getBdata(BoolVar v) const { return d_bdata[v]; }

  /** The scope level at which v was assigned. */
  uint32_t getAssignLevel(BoolVar v) const { return getBdata(v).d_scopeLvl; }

  uint32_t getAssignLevel(Literal l) const { return getAssignLevel(l.var()); }

  /** The scope level at which v was internalized. */
  uint32_t getInternLevel(BoolVar v) const
  {
    return getBdata(v).getInternLevel();
  }

  bool isMarked(BoolVar v) const { return getBdata(v).d_mark; }

  void setMark(BoolVar v)
  {
    Assert(!isMarked(v));
    getBdata(v).d_mark = true;
  }

  void unsetMark(BoolVar v)
  {
    Assert(isMarked(v));
    getBdata(v).d_mark = false;
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

  const LiteralVector& assignedLiterals() const { return d_assignedLiterals; }

  BJustification getJustification(BoolVar v) const
  {
    return getBdata(v).justification();
  }

  void setJustification(BoolVar v, BoolVarData& d, const BJustification& j);

  void assign(Literal l, const BJustification& j, bool decision = false)
  {
    Assert(l != s_falseLiteral);
    Assert(l != s_nullLiteral);
    switch (getAssignment(l))
    {
      case L_FALSE: setConflict(j, ~l); break;
      case L_UNDEF: assignCore(l, j, decision); break;
      case L_TRUE: return;
    }
  }

  void assign(Literal l, Justification* j, bool decision = false)
  {
    assign(l,
           j != nullptr ? BJustification(j) : BJustification::mkAxiom(),
           decision);
  }

  void assignCore(Literal l, BJustification j, bool decision = false);

  /** The position in the assignment of the next literal bcp visits. */
  size_t getQhead() const { return d_qhead; }

  void setQhead(size_t qhead) { d_qhead = qhead; }

  /** Boolean constraint propagation; returns false on a conflict. */
  bool bcp();

  // -------------------------------------------------------------- conflicts
  void setConflict(const BJustification& js, Literal notL);

  void setConflict(const BJustification& js) { setConflict(js, s_nullLiteral); }

  void setConflict(Justification* js)
  {
    Assert(js != nullptr);
    setConflict(BJustification(js));
  }

  bool inconsistent() const
  {
    return d_conflict != s_nullBJustification || d_assertedInconsistent;
  }

  BJustification getConflict() const { return d_conflict; }

  Literal getNotL() const { return d_notL; }

  /** Record that a formula asserted false. */
  void setAssertedInconsistent() { d_assertedInconsistent = true; }

  bool isAssertedInconsistent() const { return d_assertedInconsistent; }

  // ------------------------------------------------------------- heuristics
  const std::vector<double>& getActivityVector() const { return d_activity; }

  double getActivity(BoolVar v) const { return d_activity[v]; }

  void setActivity(BoolVar v, double act) { d_activity[v] = act; }

  void activityChanged(BoolVar v, bool increased)
  {
    if (increased)
    {
      d_caseSplitQueue->activityIncreasedEh(v);
    }
    else
    {
      d_caseSplitQueue->activityDecreasedEh(v);
    }
  }

  void incBvarActivity(BoolVar v, double inc = 1.0)
  {
    double& act = d_activity[v];
    act += d_bvarInc * inc;
    if (act > s_activityLimit)
    {
      rescaleBoolVarActivity();
    }
    d_caseSplitQueue->activityIncreasedEh(v);
  }

  void decayBvarActivity() { d_bvarInc *= d_params.d_invDecay; }

  uint64_t getBirthdate(BoolVar v) const { return d_birthdate[v]; }

  /**
   * Force the given phase the next time v is case split. Has no effect if
   * phase caching is disabled.
   */
  void forcePhase(BoolVar v, bool phase)
  {
    BoolVarData& d = getBdata(v);
    d.d_phaseAvailable = true;
    d.d_phase = phase;
  }

  void forcePhase(Literal l) { forcePhase(l.var(), !l.sign()); }

  void setTrueFirstFlag(BoolVar v);

  bool tryTrueFirst(BoolVar v) const { return getBdata(v).tryTrueFirst(); }

  /** The phase to assign the decision variable var, true for positive. */
  bool guess(BoolVar var, LBool phase);

  void updatePhaseCacheCounter();

  void forgetPhaseOfVarsInCurrentLevel();

  // -------------------------------------------------------------- relevancy
  uint32_t relevancyLvl() const
  {
    return std::min(d_relevancyLvl, d_params.d_relevancyLvl);
  }

  bool relevancy() const { return relevancyLvl() > 0; }

  /** The relevancy level chosen when the context was configured. */
  uint32_t getConfiguredRelevancyLvl() const { return d_relevancyLvl; }

  void setConfiguredRelevancyLvl(uint32_t lvl) { d_relevancyLvl = lvl; }

  /**
   * Whether an assigned atom other than a quantifier reaches the theories
   * only once it is relevant: at relevancy level 2, unless
   * --no-z3-relevancy-deliver.
   */
  bool relevancyGatesAtoms() const
  {
    return relevancyLvl() >= 2 && d_params.d_relevancyDeliver;
  }

  RelevancyPropagator& getRelevancyPropagator()
  {
    return *d_relevancyPropagator;
  }

  bool isRelevantCore(TNode n) const
  {
    return d_relevancyPropagator->isRelevant(n);
  }

  bool isRelevantCore(Literal l) const
  {
    return isRelevantCore(boolVar2Expr(l.var()));
  }

  bool isRelevant(TNode n) const { return !relevancy() || isRelevantCore(n); }

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

  template <typename Eh>
  RelevancyEh* mkRelevancyEh(const Eh& eh)
  {
    return d_relevancyPropagator->mkRelevancyEh(eh);
  }

  void addRelevancyEh(TNode source, RelevancyEh* eh)
  {
    d_relevancyPropagator->addHandler(source, eh);
  }

  void addRelevancyDependency(TNode source, TNode target)
  {
    d_relevancyPropagator->addDependency(source, target);
  }

  void addRelWatch(Literal l, RelevancyEh* eh)
  {
    d_relevancyPropagator->addWatch(boolVar2Expr(l.var()), !l.sign(), eh);
  }

  void addRelWatch(Literal l, TNode n)
  {
    d_relevancyPropagator->addWatch(boolVar2Expr(l.var()), !l.sign(), n);
  }

  /**
   * The event handler invoked by the relevancy propagator when n becomes
   * relevant. This side requeues an assigned atom that now reaches the theory
   * side, and notifies the case split queue; then the theory side is
   * notified.
   */
  void relevantEh(TNode n);

  /** Destroy the relevancy propagator, when the context is flushed. */
  void flushRelevancy() { d_relevancyPropagator.reset(nullptr); }

  double getAgility() const { return d_agility; }

  CaseSplitQueue& getCaseSplitQueue() { return *d_caseSplitQueue; }

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

  /**
   * Assert the root formula n, after the theory side has internalized its
   * subterms, as a theory lemma whose literals are the disjuncts of n, which
   * survives backtracking and garbage collection (--z3-qi-permanent). As Z3
   * does for the theory lemmas it reinitializes, every literal is marked
   * relevant; with --z3-qi-permanent-local, n is instead a root of the
   * current scope only, for relevancy and the case split queue, as a scoped
   * instance is (see reactivatePermanentRoot). Returns false if the lemma is
   * a single literal, which is asserted at the current scope only.
   */
  bool assertPermanentLemma(TNode n);

  /**
   * Make the permanent lemma n, asserted by assertPermanentLemma under
   * --z3-qi-permanent-local, a root again in the current scope, when matching
   * finds the instance again.
   */
  void reactivatePermanentRoot(TNode n);

  /** The statistics, shared with the theory side. */
  Statistics& getStats() { return d_stats; }

  /**
   * A value of the theory side's random number generator, which the case
   * split queue shares with the theories.
   */
  int getRandomValue();

  /** See SmtContext::isExtDiseqAtom. */
  bool isExtDiseqAtom(BoolVar v);

  /** See SmtContext::conflictResolutionEh. */
  void conflictResolutionEh(BoolVar v);

  // ------------------------------------------------------------ host mode
  // With --z3-prop-engine=cvc5, cvc5's prop engine searches, and this class
  // mirrors, for the theory side, the assignment of the atoms that cvc5
  // asserts: it never decides or resolves a conflict itself. Its scopes
  // follow cvc5's SAT context. See ARCHITECTURE_PLAN.md, section 15.

  /**
   * Enter host mode and prepare the search as check() does: configure the
   * theory side, internalize the asserted formulas and start the search.
   */
  void hostInit();
  /** Whether host mode is on. */
  bool isHosted() const { return d_hosted; }
  /** Push or pop scopes until the scope level is lvl. */
  void hostSyncLevel(uint32_t lvl);
  /**
   * The literal of n, an atom or a negated atom, internalizing the atom if
   * it is not internalized, for instance because it was deleted on
   * backtracking.
   */
  Literal hostLiteral(TNode n);
  /**
   * Assign l, which the host asserted. If l is false here, return false and
   * set conflict to host literals that are true in the host and contradict
   * each other, l among them.
   */
  bool hostAssign(Literal l, std::vector<Literal>& conflict);
  /**
   * Whether the value of v was asserted by the host before this side derived
   * it; explanations stop at such variables.
   */
  bool isHostAssigned(BoolVar v) const
  {
    return v < d_hostAssigned.size() && d_hostAssigned[v];
  }
  /**
   * Set out to the host literals, above the base level, that imply the
   * assigned literal l through the justifications of this side.
   */
  void hostExplain(Literal l, std::vector<Literal>& out);
  /** As hostExplain, for the current conflict. */
  void hostExplainConflict(std::vector<Literal>& out);
  /** Record the formula n, an instance, to be asserted by the host. */
  void hostRecordLemma(TNode n) { d_hostLemmas.push_back(n); }
  /**
   * Move to out the formulas recorded for the host since the last call:
   * instances, and the clauses of theory axioms and lemmas.
   */
  void hostTakeLemmas(std::vector<Node>& out);
  /** Propagate to a fixpoint; returns false on a conflict. */
  bool hostPropagate() { return propagate(); }
  /** Run the theory side's final check. */
  FinalCheckStatus hostFinalCheck(Failure& f);

  /**
   * Add the clauses that define the Boolean variable of the gate n in terms
   * of its arguments, and the relevancy watches of n. Called once, when the
   * variable of n is made.
   */
  void mkGateConstraints(TNode n);

  void mkGateClause(size_t numLits, Literal* lits);
  void mkGateClause(Literal l1, Literal l2);
  void mkGateClause(Literal l1, Literal l2, Literal l3);
  void mkGateClause(Literal l1, Literal l2, Literal l3, Literal l4);

  // ---------------------------------------------------------------- clauses
  Clause* mkClause(size_t numLits,
                   Literal* lits,
                   Justification* j,
                   ClauseKind k = CLS_AUX,
                   ClauseDelEh* delEh = nullptr);

  void mkClause(Literal l1, Literal l2, Justification* j);

  void mkClause(Literal l1, Literal l2, Literal l3, Justification* j);

  const ClauseVector& getLemmas() const { return d_lemmas; }

  size_t getNumAuxClauses() const { return d_auxClauses.size(); }

  /** The expression of each Boolean variable, indexed by the variable. */
  const std::vector<Node>& getBoolVar2ExprMap() const { return d_boolVar2Expr; }

  const WatchList& getWatch(Literal l) const { return d_watches[l.index()]; }

  bool binaryClauseOptEnabled() const { return d_params.d_binaryClauseOpt; }

  /** Simplify the clauses at the base level, when there is new work. */
  void simplifyClauses();

  size_t getNumUnitsToReassert() const { return d_unitsToReassert.size(); }

  void addUnitToReassert(TNode unit, bool sign, bool relevant)
  {
    d_unitsToReassert.push_back(ReplayUnit{unit, sign, relevant});
  }

  /**
   * Cache the generations of the atoms of the clauses and units that will be
   * reinitialized when backtracking to newScopeLvl.
   */
  void cacheGeneration(uint32_t newScopeLvl);

  /** Cache the generations of the atoms of lits that newScopeLvl deletes. */
  void cacheGeneration(size_t numLits,
                       const Literal* lits,
                       uint32_t newScopeLvl);

  /**
   * Reinitialize the lemmas that contain Boolean variables deleted during
   * backtracking numScopes levels; numBoolVars is the number of variables
   * that survived.
   */
  void reinitClauses(size_t numScopes, size_t numBoolVars);

  void reassertUnits(size_t unitsToReassertLim);

  // ----------------------------------------------------------------- scopes
  uint32_t getScopeLevel() const { return d_scopeLvl; }

  uint32_t getBaseLevel() const { return d_baseLvl; }

  bool atBaseLevel() const { return d_scopeLvl == d_baseLvl; }

  uint32_t getSearchLevel() const { return d_searchLvl; }

  bool atSearchLevel() const { return d_scopeLvl == d_searchLvl; }

  void setSearchLevel(uint32_t lvl) { d_searchLvl = lvl; }

  /** The position in the assignment stack of the decision at scopeLvl. */
  size_t getDecisionLiteralPos(uint32_t scopeLvl) const
  {
    Assert(scopeLvl > d_baseLvl);
    return d_scopes[scopeLvl - 1].d_assignedLiteralsLim;
  }

  /** Open a new search scope, on both sides. */
  void pushScope();

  /** Open a new user scope, after pushScope. */
  void pushBaseScope();

  /** Backtrack numScopes scopes, on both sides. */
  void popScope(size_t numScopes);

  /** Backtrack to the base (user) level. */
  void popToBaseLvl();

  /** Backtrack to the search level. */
  void popToSearchLvl();

  // ---------------------------------------------------------- search driver
  /** Run the search, from the search level. */
  LBool search();

  /** Propagate to a fixpoint; returns false on a conflict. */
  bool propagate();

  /** Whether either side has propagation work pending. */
  bool canPropagate() const;

  /**
   * Resolve the current conflict, learning a clause and backjumping. Returns
   * false if the conflict is at the search level, i.e. unsatisfiable.
   */
  bool resolveConflict();

  /** True if the search was interrupted or ran out of resources. */
  bool getCancelFlag();

  void interrupt() { d_interrupted = true; }

  bool resourceLimitsExceeded();

  Failure getLastSearchFailure() const { return d_lastSearchFailure; }

  void setLastSearchFailure(Failure f) { d_lastSearchFailure = f; }

  bool isSearching() const { return d_searching; }

  uint64_t getNumConflicts() const { return d_numConflicts; }

  /** Reset the state of conflict resolution before a check. */
  void resetConflictResolution();

 private:
  struct Scope
  {
    size_t d_assignedLiteralsLim;
    size_t d_auxClausesLim;
    size_t d_unitsToReassertLim;
  };

  struct BaseScope
  {
    size_t d_lemmasLim;
    size_t d_simpQheadLim;
    bool d_inconsistent;
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

  static constexpr double s_activityLimit = 1e100;
  static constexpr double s_invActivityLimit = 1e-100;

  void rescaleBoolVarActivity();
  void addScores(size_t n, const Literal* lits);
  void unassignVars(size_t oldLim);

  // the Boolean structure
  void assertDefault(TNode n);
  void assertDistinct(TNode n);
  void mkRootClause(size_t numLits, Literal* lits);
  void mkRootClause(Literal l1, Literal l2);
  void mkRootClause(Literal l1, Literal l2, Literal l3);
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
  void recordRelevancy(size_t n, const Literal* lits);
  void restoreRelevancy(size_t n, const Literal* lits);

  bool checkPreamble();
  LBool checkFinalize(LBool r);

  // search driver
  /** Reset the search state and the heuristics at the start of a search. */
  void initSearch();
  void endSearch();
  void incLimits();
  bool restart(LBool& status, uint32_t currLvl);
  void tick(uint32_t& counter) const;
  LBool boundedSearch();
  bool decide();
  /** Delete inactive lemmas, by the configured strategy. */
  void delInactiveLemmas();
  /**
   * Backtrack numScopes scopes, without resetting the cached generations, and
   * return the number of Boolean variables before the clauses are
   * reinitialized, which is what tells reinitClauses which variables were
   * deleted.
   */
  size_t popScopeCore(size_t numScopes);
  size_t popClauses(uint32_t newLvl);
  void unassignToScope(uint32_t newLvl);
  void popScopeLevels(uint32_t newLvl);

  // clause management
  bool trackOccs() const { return d_params.d_phaseSelection == PS_OCCURRENCE; }
  void decRef(Literal l);
  void incRef(Literal l);
  void removeLitOccs(const Clause& cls, size_t numBoolVars);
  void addLitOccs(const Clause& cls);
  void removeWatchLiteral(Clause* cls, size_t idx);
  void removeWatch(BoolVar v);
  void removeClsOccs(Clause* cls);
  void delClause(Clause* cls);
  void delClauses(ClauseVector& v, size_t oldSize);
  bool isUnitClause(const Clause* c) const;
  bool isEmptyClause(const Clause* c) const;
  void cacheGeneration(const Clause* cls, uint32_t newScopeLvl);
  bool simplifyAuxClauseLiterals(size_t& numLits,
                                 Literal* lits,
                                 LiteralVector& simpLits);
  bool simplifyAuxLemmaLiterals(size_t& numLits, Literal* lits);
  void markForReinit(Clause* cls, uint32_t scopeLvl, bool reinternalizeAtoms);
  uint32_t getMaxIscopeLvl(size_t numLits, const Literal* lits) const;
  bool useBinaryClauseOpt(Literal l1, Literal l2, bool lemma) const;
  int selectLearnedWatchLit(const Clause* cls) const;
  int selectWatchLit(const Clause* cls, int startingAt) const;
  void addWatchLiteral(Clause* cls, size_t idx);
  bool simplifyClause(Clause& cls);
  size_t simplifyClauses(ClauseVector& clauses, size_t startingAt);
  bool isJustifying(Clause* cls) const
  {
    for (size_t i = 0; i < 2; ++i)
    {
      BJustification js = getJustification((*cls)[i].var());
      if (js.getKind() == BJustification::CLAUSE && js.getClause() == cls)
      {
        return true;
      }
    }
    return false;
  }
  /** Mark the root n relevant, as assertRoot does. */
  void markRootRelevant(TNode n);

  /** Push to todo the antecedents of consequent under js. */
  void hostAntecedents(Literal consequent,
                       const BJustification& js,
                       std::vector<Literal>& todo);
  /**
   * Expand the literals of todo through their justifications down to host
   * literals, which are appended to out; literals of the base level are
   * dropped, as they are permanent.
   */
  void hostExpand(std::vector<Literal>& todo, std::vector<Literal>& out);

  /**
   * Whether cls is a permanent instance whose relevancy is scoped
   * (--z3-qi-permanent-local); reinitializing it does not mark its literals
   * relevant.
   */
  bool isLocalPermanent(const Clause* cls) const
  {
    return cls->isPermanent() && d_params.d_qiPermanentLocal;
  }

  bool canDelete(Clause* cls) const
  {
    if (cls->inReinitStack() || cls->isPermanent())
    {
      return false;
    }
    return !isJustifying(cls);
  }
  void delInactiveLemmas1();
  void delInactiveLemmas2();
  bool moreThanKUnassignedLiterals(Clause* cls, size_t k);

  /** Whether host mode is on; see hostInit. */
  bool d_hosted = false;
  /** For each variable, whether its value was asserted by the host. */
  std::vector<bool> d_hostAssigned;
  /** The formulas recorded for the host; see hostTakeLemmas. */
  std::vector<Node> d_hostLemmas;

  /** The theory side. */
  SmtContext& d_ctx;
  Params& d_params;
  Statistics& d_stats;

  /** The relevancy level chosen when the context was configured. */
  uint32_t d_relevancyLvl;
  std::unique_ptr<RelevancyPropagator> d_relevancyPropagator;
  /** Scratch space for recordRelevancy and restoreRelevancy. */
  std::vector<bool> d_relevantConflictLiterals;

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
  /** The occurrence count of each literal. */
  std::vector<uint32_t> d_litOccs;
  std::vector<BoolVarData> d_bdata;
  std::vector<double> d_activity;
  std::vector<double> d_litScores[2];
  std::vector<uint64_t> d_birthdate;
  ClauseVector d_auxClauses;
  ClauseVector d_lemmas;
  std::vector<ClauseVector> d_clausesToReinit;
  std::vector<ReplayUnit> d_unitsToReassert;
  LiteralVector d_assignedLiterals;
  size_t d_qhead;
  size_t d_simpQhead;
  /** The budget for clause simplification; it may become negative. */
  int64_t d_simpCounter;
  std::unique_ptr<CaseSplitQueue> d_caseSplitQueue;
  double d_bvarInc;
  bool d_phaseCacheOn;
  /** Used to decide when to turn phase caching on and off. */
  uint32_t d_phaseCounter;
  /** The default phase when phase caching is in use. */
  bool d_phaseDefault;
  /** How often assignments flip their cached phase; drives restarts. */
  double d_agility;

  /*
    A conflict is usually a single justification, i.e. a justification for
    false. If d_notL is not the null literal then d_conflict justifies l, and
    the conflict is the union of d_notL and d_conflict.
  */
  BJustification d_conflict;
  Literal d_notL;
  /** True if a formula asserted false. */
  bool d_assertedInconsistent;
  /** Set while the clauses are deleted on flushing. */
  bool d_flushing;

  /** The formulas asserted to the core, and how far they are internalized. */
  std::vector<Node> d_assertedFormulas;
  size_t d_assertedFormulasQhead;
  bool d_hasQuantifiers;
  bool d_internalizingAssertions;
  /** Why the last search answered L_UNDEF. */
  std::string d_unknown;

  std::unique_ptr<ConflictResolution> d_conflictResolution;

  // search driver
  Failure d_lastSearchFailure;
  bool d_searching;
  bool d_interrupted;
  uint64_t d_numConflicts;
  uint64_t d_numConflictsSinceRestart;
  uint64_t d_numConflictsSinceLemmaGc;
  uint64_t d_numRestarts;
  uint64_t d_restartThreshold;
  uint64_t d_restartOuterThreshold;
  uint32_t d_lubyIdx;
  uint64_t d_lemmaGcThreshold;

  uint32_t d_scopeLvl;
  uint32_t d_baseLvl;
  /**
   * Greater than d_baseLvl when assumptions are used, and equal to it
   * otherwise.
   */
  uint32_t d_searchLvl;
  std::vector<Scope> d_scopes;
  std::vector<BaseScope> d_baseScopes;

  MkBoolVarTrail d_mkBoolVarTrail;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__PROP_CORE_H */
