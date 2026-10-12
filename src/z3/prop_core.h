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

#include <memory>
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
#include "z3/statistics.h"
#include "z3/types.h"
#include "z3/util/literal.h"
#include "z3/util/trail.h"
#include "z3/util/util.h"
#include "z3/watch_list.h"

namespace cvc5::internal {
namespace z3 {

class SmtContext;

/**
 * The Boolean search state of the core: the Boolean variables and their
 * assignment, the watch lists and the clauses, Boolean constraint
 * propagation, the variable activity and phase heuristics, the case split
 * queue, and the scope levels.
 *
 * This is the propositional side of the boundary described in
 * PROP_THEORY_SPLIT.md. The theory side, SmtContext, owns this object. What
 * this side asks of the theory side goes through the SmtContext reference
 * d_ctx and is limited to:
 *  - relevancy, which decides which assigned atoms are passed to the theory
 *    side and which lemma literals are marked relevant (relevancyLvl,
 *    isRelevantCore, markAsRelevant);
 *  - handing assigned atoms to the theory side (enqueueAtom);
 *  - recreating the atoms of clauses that survive backtracking (internalize,
 *    getLiteral) and caching the generations they had (cacheGeneration);
 *  - removing a deleted quantifier variable (notifyBoolVarDeleted);
 *  - the phase hint of a theory (getTheory);
 *  - the infrastructure the two sides share: the trail, the region-allocated
 *    justifications, the random number generator and the cancel flag.
 *
 * The search driver, the conflict resolution and the orchestration of scopes
 * are still in SmtContext; see PROP_THEORY_SPLIT.md, section 8, step 4(b).
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

  /** Make the case split queue, which the theory side's constructor calls. */
  void finishInit();
  /** Make the variable of t, the constant true, assigned by an axiom. */
  void initTrue(TNode t);
  /** Delete all clauses, when the context is flushed. */
  void flushClauses();

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

  double getAgility() const { return d_agility; }

  CaseSplitQueue& getCaseSplitQueue() { return *d_caseSplitQueue; }

  /** Reset the heuristics at the start of a search. */
  void initSearch();

  void endSearch();

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

  /** Delete inactive lemmas, by the configured strategy. */
  void delInactiveLemmas();

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

  /** Open a new search scope. */
  void pushScope();

  /** Open a new user scope, after pushScope. */
  void pushBaseScope();

  /**
   * The first part of backtracking to newLvl: delete the clauses that do not
   * survive it and reset the conflict. Returns the number of delayed units to
   * keep, to be passed to reassertUnits.
   */
  size_t popClauses(uint32_t newLvl);

  /** Unassign the literals assigned at a scope above newLvl. */
  void unassignToScope(uint32_t newLvl);

  /** Close the scopes above newLvl. */
  void popScopeLevels(uint32_t newLvl);

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
  bool canDelete(Clause* cls) const
  {
    if (cls->inReinitStack())
    {
      return false;
    }
    return !isJustifying(cls);
  }
  void delInactiveLemmas1();
  void delInactiveLemmas2();
  bool moreThanKUnassignedLiterals(Clause* cls, size_t k);

  /** The theory side. */
  SmtContext& d_ctx;
  Params& d_params;
  Statistics& d_stats;

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
