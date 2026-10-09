/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The logical context: the ported Z3 SMT core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_context.h, and recast in cvc5 style.
 *
 * This is Z3's CDCL(T) engine. It owns the Boolean search (watch lists,
 * propagation, conflict resolution, restarts, lemma garbage collection), the
 * E-graph (congruence closure over enodes), relevancy propagation, the
 * case-split queue, the theory plugins, and the quantifier manager.
 *
 * What is deliberately not ported: proof production, the user propagator,
 * parallel and lookahead search, consequence finding, Z3's asserted_formulas
 * preprocessing pipeline (cvc5's Preprocessor is used instead), lambdas, and
 * Z3's label literals.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__SMT_CONTEXT_H
#define CVC5__Z3__SMT_CONTEXT_H

#include <deque>
#include <memory>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "util/statistics_stats.h"
#include "z3/ast.h"
#include "z3/b_justification.h"
#include "z3/bool_var_data.h"
#include "z3/case_split_queue.h"
#include "z3/cg_table.h"
#include "z3/clause.h"
#include "z3/conflict_resolution.h"
#include "z3/dyn_ack.h"
#include "z3/enode.h"
#include "z3/eq_justification.h"
#include "z3/fingerprints.h"
#include "z3/justification.h"
#include "z3/nnf.h"
#include "z3/params.h"
#include "z3/pattern_inference.h"
#include "z3/push_app_ite.h"
#include "z3/relevancy.h"
#include "z3/statistics.h"
#include "z3/theory.h"
#include "z3/types.h"
#include "z3/util/literal.h"
#include "z3/util/random_gen.h"
#include "z3/util/trail.h"
#include "z3/util/uint_set.h"
#include "z3/util/util.h"
#include "z3/watch_list.h"

namespace cvc5::internal {
namespace z3 {

class ModelGenerator;
class QuantifierManager;
class Cvc5Bridge;

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

/** How the core is configured. Z3's config_mode. */
enum ConfigMode
{
  /** no automatic configuration */
  CFG_BASIC,
  /** configure from the logic */
  CFG_LOGIC,
  /** configure from the static features of the input */
  CFG_AUTO
};

class SmtContext : protected EnvObj
{
  friend class ModelGenerator;
  friend class ConflictResolution;
  friend class DynAckManager;
  friend class QuantifierManager;

 public:
  /** The search statistics. Public, as in Z3. */
  Statistics d_stats;
  /**
   * Handles keeping the counters above registered with cvc5. A deque is used
   * because a ReferenceStat detaches from its counter when a copy of it is
   * destroyed, so the stored handles must never be relocated.
   */
  std::deque<ReferenceStat<uint64_t>> d_regStats;

  SmtContext(Env& env, Params& p);
  virtual ~SmtContext();

  SmtContext(const SmtContext&) = delete;
  SmtContext& operator=(const SmtContext&) = delete;

  // --------------------------------------------------------------- setup
  /** Register a theory plugin. Takes ownership. */
  void registerPlugin(Theory* th);

  /**
   * Configure the core. A logical context can only be configured at scope
   * level zero and before internalizing any formula.
   */
  virtual void setupContext(bool useStaticFeatures);

  void setupComponents();

  ConfigMode getConfigMode(bool useStaticFeatures) const;

  // ---------------------------------------------------------- assertions
  /** Assert a (preprocessed) formula. */
  void assertFormula(TNode e);

  /** Add e to the asserted formulas, splitting a top-level conjunction. */
  void pushAssertion(TNode e);

  /** A development hook: dump the assigned relevant literals to a file. */
  void dumpCandidateModel(const char* path);

  /** Write what the core was given, as a parsable benchmark. */
  void dumpAssertions(const char* path);

  /** A development hook: check the candidate model with a cvc5 subsolver. */
  void checkCandidateModel();

  /** Internalize the assertions that have not been internalized yet. */
  void internalizeAssertions();

  size_t getNumAssertedFormulas() const { return d_assertedFormulas.size(); }

  TNode getAssertedFormula(size_t idx) const { return d_assertedFormulas[idx]; }

  // -------------------------------------------------------------- search
  /** Run the search. */
  LBool check(size_t numAssumptions = 0, const Node* assumptions = nullptr);

  /** Configure the core and then run the search. */
  LBool setupAndCheck();

  void push();
  void pop(size_t numScopes);

  /** Backtrack to the base (user) level. */
  void popToBaseLvl();

  Failure getLastSearchFailure() const { return d_lastSearchFailure; }

  void setReasonUnknown(const std::string& msg) { d_unknown = msg; }

  const std::string& getReasonUnknown() const { return d_unknown; }

  std::ostream& printLastFailure(std::ostream& out) const;

  size_t getUnsatCoreSize() const { return d_unsatCore.size(); }

  TNode getUnsatCoreExpr(size_t idx) const { return d_unsatCore[idx]; }

  const std::vector<Node>& unsatCore() const { return d_unsatCore; }

  // ----------------------------------------------------------- accessors
  Params& getParams() { return d_params; }

  const Params& getParams() const { return d_params; }

  Statistics& getStats() { return d_stats; }

  Region& getRegion() { return d_region; }

  bool relevancy() const { return relevancyLvl() > 0; }

  uint32_t relevancyLvl() const;

  ENode* getENode(TNode n) const
  {
    Assert(eInternalized(n));
    return d_app2ENode[n.getId()];
  }

  /** Like getENode, but returns null if n is not internalized. */
  ENode* findENode(TNode n) const
  {
    return getx(d_app2ENode, n.getId(), static_cast<ENode*>(nullptr));
  }

  void resetBoolVars() { d_expr2BoolVar.clear(); }

  BoolVar getBoolVar(TNode n) const { return d_expr2BoolVar[n.getId()]; }

  BoolVar getBoolVar(const ENode* n) const { return getBoolVar(n->getExpr()); }

  BoolVar getBoolVarOfId(size_t id) const { return d_expr2BoolVar[id]; }

  BoolVar getBoolVarOfIdOption(size_t id) const
  {
    return getx(d_expr2BoolVar, id, s_nullBoolVar);
  }

  void setBoolVar(size_t id, BoolVar v)
  {
    setx(d_expr2BoolVar, id, v, s_nullBoolVar);
  }

  const ClauseVector& getLemmas() const { return d_lemmas; }

  Literal getLiteral(TNode n) const;

  bool hasENode(BoolVar v) const { return d_bdata[v].isENode(); }

  ENode* boolVar2ENode(BoolVar v) const
  {
    Assert(d_bdata[v].isENode());
    return d_app2ENode[d_boolVar2Expr[v].getId()];
  }

  BoolVar enode2BoolVar(const ENode* n) const
  {
    Assert(n->isBool());
    Assert(n != d_falseENode);
    return getBoolVarOfId(n->getOwnerId());
  }

  Literal enode2Literal(const ENode* n) const
  {
    Assert(n->isBool());
    return n == d_falseENode ? s_falseLiteral : Literal(enode2BoolVar(n));
  }

  size_t getNumBoolVars() const { return d_bInternalizedStack.size(); }

  BoolVarData& getBdata(BoolVar v) { return d_bdata[v]; }

  const BoolVarData& getBdata(BoolVar v) const { return d_bdata[v]; }

  LBool getLitAssignment(size_t litIdx) const
  {
    return static_cast<LBool>(d_assignment[litIdx]);
  }

  LBool getAssignment(Literal l) const { return getLitAssignment(l.index()); }

  LBool getAssignment(BoolVar v) const { return getAssignment(Literal(v)); }

  const LiteralVector& assignedLiterals() const { return d_assignedLiterals; }

  const WatchList& getWatch(Literal l) const { return d_watches[l.index()]; }

  LBool getAssignment(TNode n) const;

  /** Like getAssignment, but returns L_UNDEF if n is not internalized. */
  LBool findAssignment(TNode n) const;

  LBool getAssignment(ENode* n) const;

  BJustification getJustification(BoolVar v) const
  {
    return getBdata(v).justification();
  }

  void setJustification(BoolVar v, BoolVarData& d, const BJustification& j);

  bool hasThJustification(BoolVar v, TheoryId thId) const
  {
    BJustification js = getJustification(v);
    return js.getKind() == BJustification::JUSTIFICATION
           && js.getJustification()->getFromTheory() == thId;
  }

  void setRandomSeed(uint32_t s) { d_random.setSeed(s); }

  int getRandomValue() { return d_random(); }

  bool isSearching() const { return d_searching; }

  const std::vector<double>& getActivityVector() const { return d_activity; }

  double getActivity(BoolVar v) const { return d_activity[v]; }

  uint64_t getNumAssignments() const { return d_stats.d_numAssignments; }

  uint64_t getBirthdate(BoolVar v) const { return d_birthdate[v]; }

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

  bool isAssumption(BoolVar v) const { return getBdata(v).d_assumption; }

  bool isAssumption(Literal l) const { return isAssumption(l.var()); }

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

  /** The scope level at which v was assigned. */
  uint32_t getAssignLevel(BoolVar v) const { return getBdata(v).d_scopeLvl; }

  uint32_t getAssignLevel(Literal l) const { return getAssignLevel(l.var()); }

  /** The scope level at which v was internalized. */
  uint32_t getInternLevel(BoolVar v) const
  {
    return getBdata(v).getInternLevel();
  }

  Theory* getTheory(TheoryId thId) const
  {
    return thId == s_nullTheoryId ? nullptr : d_theories[thId];
  }

  const std::vector<Theory*>& theories() const { return d_theorySet; }

  uint32_t getScopeLevel() const { return d_scopeLvl; }

  uint32_t getBaseLevel() const { return d_baseLvl; }

  bool atBaseLevel() const { return d_scopeLvl == d_baseLvl; }

  uint32_t getSearchLevel() const { return d_searchLvl; }

  bool atSearchLevel() const { return d_scopeLvl == d_searchLvl; }

  void popToSearchLevel() { popToSearchLvl(); }

  bool trackingAssumptions() const
  {
    return !d_assumptions.empty() && d_searchLvl > d_baseLvl;
  }

  TNode boolVar2Expr(BoolVar v) const { return d_boolVar2Expr[v]; }

  Node literal2Expr(Literal l) const;

  bool isTrue(const ENode* n) const { return n == d_trueENode; }

  bool isFalse(const ENode* n) const { return n == d_falseENode; }

  size_t getNumENodesOf(TNode decl) const
  {
    uint32_t id = getDeclIdOption(decl);
    return id < d_decl2ENodes.size() ? d_decl2ENodes[id].size() : 0;
  }

  const ENodeVector& enodesOf(TNode decl) const
  {
    uint32_t id = getDeclIdOption(decl);
    return id < d_decl2ENodes.size() ? d_decl2ENodes[id] : d_emptyVector;
  }

  const ENodeVector& enodes() const { return d_enodes; }

  uint32_t getGeneration(TNode q) const;

  uint32_t getGeneration(ENode* e) const
  {
    // Patterns with equalities are not supported, so there is no need to
    // track the generation of equality nodes.
    if (e->isEq())
    {
      return 0;
    }
    return getCgRoot(e)->d_generation;
  }

  uint32_t getMaxGeneration(size_t numENodes, ENode* const* enodes)
  {
    uint32_t max = 0;
    for (size_t i = 0; i < numENodes; ++i)
    {
      uint32_t curr = getGeneration(enodes[i]);
      if (curr > max)
      {
        max = curr;
      }
    }
    return max;
  }

  void setGeneration(ENode* e, uint32_t generation);

  /** True if the core internalized universal quantifiers. */
  bool internalizedQuantifiers() const;

  /** True if the input contains universal quantifiers. */
  bool hasQuantifiers() const { return d_hasQuantifiers; }

  Fingerprint* addFingerprint(uint64_t data,
                              uint32_t dataHash,
                              size_t numArgs,
                              ENode* const* args)
  {
    return d_fingerprints.insert(data, dataHash, numArgs, args);
  }

  TheoryId getVarTheory(BoolVar v) const { return getBdata(v).getTheory(); }

  void setVarTheory(BoolVar v, TheoryId tid);

  QuantifierManager* getQuantifierManager() { return d_qmanager.get(); }

  // ----------------------------------------------- backtracking support
  template <typename TrailObject>
  void pushTrail(const TrailObject& obj)
  {
    d_trailStack.push(obj);
  }

  void pushTrailPtr(Trail* ptr) { d_trailStack.pushPtr(ptr); }

  TrailStack& getTrailStack() { return d_trailStack; }

  // ------------------------------------------------------ internalization
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

  bool eInternalized(TNode n) const
  {
    return getx(d_app2ENode, n.getId(), static_cast<ENode*>(nullptr))
           != nullptr;
  }

  size_t getNumBInternalized() const { return d_bInternalizedStack.size(); }

  TNode getBInternalized(size_t idx) const { return d_bInternalizedStack[idx]; }

  size_t getNumEInternalized() const { return d_eInternalizedStack.size(); }

  TNode getEInternalized(size_t idx) const { return d_eInternalizedStack[idx]; }

  /** The position in the assignment stack of the decision at scopeLvl. */
  size_t getDecisionLiteralPos(uint32_t scopeLvl) const
  {
    Assert(scopeLvl > d_baseLvl);
    return d_scopes[scopeLvl - 1].d_assignedLiteralsLim;
  }

  bool binaryClauseOptEnabled() const { return d_params.d_binaryClauseOpt; }

  /** The canonicalizer for quantifiers; see z3/ast.h. */
  QuantifierNormalizer& getNormalizer() { return d_normalizer; }

  PatternInference& getPatternInference() { return d_patternInference; }

  ConnectiveNormalizer& getConnectiveNormalizer() { return d_connNormalizer; }

  AssertionRewriter& getAssertionRewriter() { return d_assertionRewriter; }

  Nnf& getNnf() { return d_nnf; }

  /** Z3's ng_lift_ite step; see z3/push_app_ite.h. */
  NgPushAppIte& getNgPushAppIte() { return d_ngPushAppIte; }

  /** The environment of the enclosing cvc5 solver. */
  const Env& getEnv() const { return d_env; }

  /** The shared state of the bridges to cvc5's own theory solvers. */
  Cvc5Bridge& getCvc5Bridge();

  /**
   * Record that the input uses a construct this port does not support, so
   * that the search answers "unknown" instead of guessing.
   */
  void markUnsupported() { d_unsupported = true; }

  bool isUnsupported() const { return d_unsupported; }

  /** A diagnostic flag: set while the forced rematch runs. */
  bool d_inForcedRematch = false;

  /**
   * Internalize the body of a quantifier instance. Unlike a plain assertion,
   * the case split queue is told about it, so that a relevancy-based queue can
   * place the new literals.
   */
  void internalizeInstance(TNode body, uint32_t generation);

  void ensureInternalized(TNode e);

  void internalize(TNode n, bool gateCtx);
  void internalize(const Node* exprs, size_t numExprs, bool gateCtx);
  void internalize(TNode n, bool gateCtx, uint32_t generation);

  ENode* nonGroundInternalize(TNode e);

  Clause* mkClause(size_t numLits,
                   Literal* lits,
                   Justification* j,
                   ClauseKind k = CLS_AUX,
                   ClauseDelEh* delEh = nullptr);

  void mkClause(Literal l1, Literal l2, Justification* j);

  void mkClause(Literal l1, Literal l2, Literal l3, Justification* j);

  void mkThClause(TheoryId tid, size_t numLits, Literal* lits, ClauseKind k);

  void mkThAxiom(TheoryId tid, size_t numLits, Literal* lits)
  {
    mkThClause(tid, numLits, lits, CLS_TH_AXIOM);
  }

  void mkThAxiom(TheoryId tid, Literal l1);
  void mkThAxiom(TheoryId tid, Literal l1, Literal l2);
  void mkThAxiom(TheoryId tid, Literal l1, Literal l2, Literal l3);

  void mkThAxiom(TheoryId tid, const LiteralVector& ls)
  {
    mkThAxiom(tid, ls.size(), const_cast<Literal*>(ls.data()));
  }

  void mkThLemma(TheoryId tid, size_t numLits, Literal* lits)
  {
    mkThClause(tid, numLits, lits, CLS_TH_LEMMA);
  }

  void mkThLemma(TheoryId tid, Literal l1, Literal l2)
  {
    Literal ls[2] = {l1, l2};
    mkThLemma(tid, 2, ls);
  }

  void mkThLemma(TheoryId tid, Literal l1, Literal l2, Literal l3)
  {
    Literal ls[3] = {l1, l2, l3};
    mkThLemma(tid, 3, ls);
  }

  void mkThLemma(TheoryId tid, const LiteralVector& ls)
  {
    mkThLemma(tid, ls.size(), const_cast<Literal*>(ls.data()));
  }

  /**
   * Tell the core that the given literals form a "theory case split": at most
   * one of them may be assigned true. The theory is assumed to have already
   * asserted that at least one of them holds.
   */
  void mkThCaseSplit(size_t numLits, Literal* lits);

  /**
   * Give the branching heuristic a priority hint for a theory-aware literal.
   * Such literals are always branched on before unmarked ones, highest
   * priority first.
   */
  void addTheoryAwareBranchingInfo(BoolVar v, double priority, LBool phase);

  // ---------------------------------------------------- trail callbacks
  /** Undo an addEq; invoked from the trail. */
  void undoAddEq(ENode* r1, ENode* n1, size_t r2NumParents);

  /** Undo a congruence class generation merge; invoked from the trail. */
  void undoMergeCgcGenerations(ENode* e1,
                               uint32_t e1Generation,
                               ENode* e2,
                               uint32_t e2Generation);

  void undoThCaseSplit(Literal l);

  bool propagateThCaseSplit(size_t qhead);

  BoolVar mkBoolVar(TNode n);

  ENode* mkENode(TNode n, bool suppressArgs, bool mergeTf, bool cgcEnabled);

  void attachThVar(ENode* n, Theory* th, TheoryVar v);

  template <typename JustificationT>
  Justification* mkJustification(const JustificationT& j)
  {
    Justification* js = new (getRegion()) JustificationT(j);
    Assert(js->inRegion());
    if (js->hasDelEh())
    {
      d_justifications.push_back(js);
    }
    return js;
  }

  void mkGateClause(size_t numLits, Literal* lits);
  void mkGateClause(Literal l1, Literal l2);
  void mkGateClause(Literal l1, Literal l2, Literal l3);
  void mkGateClause(Literal l1, Literal l2, Literal l3, Literal l4);

  void setEnodeFlag(BoolVar v, bool isNewVar);

  // ------------------------------------------------------------- engine
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

  void setTrueFirstFlag(BoolVar v);

  bool tryTrueFirst(BoolVar v) const { return getBdata(v).tryTrueFirst(); }

  bool assumeEq(ENode* lhs, ENode* rhs);

  bool isShared(ENode* n) const;

  bool isBetaRedex(ENode* p, ENode* n) const;

  void assignEq(ENode* lhs, ENode* rhs, const EqJustification& js)
  {
    pushEq(lhs, rhs, js);
  }

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

  bool containsInstance(TNode q, size_t numBindings, ENode* const* bindings);

  bool addInstance(TNode q,
                   TNode pat,
                   size_t numBindings,
                   ENode* const* bindings,
                   uint32_t maxGeneration,
                   uint32_t minTopGeneration,
                   uint32_t maxTopGeneration,
                   std::vector<std::pair<ENode*, ENode*>>& usedENodes);

  void setGlobalGeneration(uint32_t generation) { d_generation = generation; }

  void addEq(ENode* n1, ENode* n2, EqJustification js);

  void setConflict(Justification* js)
  {
    Assert(js != nullptr);
    setConflict(BJustification(js));
  }

  bool inconsistent() const
  {
    return d_conflict != s_nullBJustification || d_assertedInconsistent;
  }

  bool hasCaseSplits();

  uint64_t getNumConflicts() const { return d_numConflicts; }

  static bool isEq(const ENode* n1, const ENode* n2)
  {
    return n1->getRoot() == n2->getRoot();
  }

  ENode* getCgRoot(ENode* n) const
  {
    if (!n->usesCgTable())
    {
      return n;
    }
    // Fast path: if n is already the congruence root, avoid the table lookup.
    // This matters because getCgRoot is on every generation lookup.
    if (n->isCgr())
    {
      return n;
    }
    ENode* r = d_cgTable.find(n);
    return r != nullptr ? r : n;
  }

  bool isDiseq(ENode* n1, ENode* n2) const;

  /**
   * Check disequality using congruence and equality atoms, ignoring distinct
   * root values.
   */
  bool isDiseqNoValueCheck(ENode* n1, ENode* n2) const;

  bool isDiseqSlow(ENode* n1, ENode* n2) const;

  /**
   * An extended disequality check that looks through parents up to the given
   * depth.
   *
   * Note Z3 indexes the deep case with an "almost congruence" table, which is
   * not ported: that index exists for array extensionality, which this port
   * does not cover. The shallow case is faithful, and the deep case falls back
   * to the shallow search, which may report fewer disequalities than Z3 and so
   * only weakens a branching heuristic.
   */
  bool isExtDiseq(ENode* n1, ENode* n2, uint32_t depth);

  /** An enode congruent to decl(args), or null if there is none. */
  ENode* getENodeEqTo(TNode decl,
                      bool commutative,
                      size_t numArgs,
                      ENode* const* args);

  bool guess(BoolVar var, LBool phase);

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

  bool canPropagate() const;

  // ------------------------------------------------------------ relevancy
  /** The event handler invoked by the relevancy propagator. */
  void relevantEh(TNode n);

  bool isRelevantCore(TNode n) const
  {
    return d_relevancyPropagator->isRelevant(n);
  }

  bool isRelevant(TNode n) const { return !relevancy() || isRelevantCore(n); }

  bool isRelevant(ENode* n) const { return isRelevant(n->getExpr()); }

  bool isRelevant(BoolVar v) const { return isRelevant(boolVar2Expr(v)); }

  bool isRelevant(Literal l) const
  {
    Assert(l != s_trueLiteral && l != s_falseLiteral);
    return isRelevant(l.var());
  }

  bool isRelevantCore(Literal l) const
  {
    return isRelevantCore(boolVar2Expr(l.var()));
  }

  void markAsRelevant(TNode n)
  {
    d_relevancyPropagator->markAsRelevant(n);
    d_relevancyPropagator->propagate();
  }

  void markAsRelevant(ENode* n) { markAsRelevant(n->getExpr()); }

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

  // -------------------------------------------------- value extraction
  bool getValue(ENode* n, Node& value);

  /**
   * Rewrite a quantifier instance before it is internalized. Z3 applies its
   * th_rewriter here; this port uses cvc5's rewriter.
   */
  Node rewriteInstance(TNode n) const { return rewrite(n); }

  /**
   * A dense id for a declaration, created on demand. This is the counterpart
   * of Z3's func_decl::get_small_id, which the E-matching engine uses to index
   * its tables by function symbol.
   */
  uint32_t getDeclId(TNode decl);
  /** The dense id of decl, or UINT32_MAX if it has none yet. */
  uint32_t getDeclIdOption(TNode decl) const;

  /** The equality atom to create during the search for lhs = rhs. */
  Node mkEqAtom(TNode lhs, TNode rhs);

  // ------------------------------------------------------------ printing
  std::ostream& printLiteral(std::ostream& out, Literal l) const;
  std::ostream& printLiterals(std::ostream& out,
                              size_t numLits,
                              const Literal* lits) const;
  std::ostream& print(std::ostream& out, BJustification j) const;
  void print(std::ostream& out) const;
  void printStatistics(std::ostream& out) const;

  /**
   * Expose the core's counters through cvc5's --stats, so that the search
   * behavior can be compared against Z3's own -st output.
   */
  void registerStatistics();

  /**
   * Record that a term of theory tid was internalized with no plugin to
   * reason about it. The core then treats the term as uninterpreted, which
   * only drops constraints: "unsat" stays sound, but "sat" does not, so the
   * result is weakened to "unknown".
   */
  void markModelUnsound(TheoryId tid);

  /** True if any theory was internalized without a plugin. */
  bool isModelUnsound() const { return !d_modelUnsoundTheories.empty(); }

  bool resourceLimitsExceeded();

  bool getCancelFlag();

  void interrupt() { d_interrupted = true; }

 protected:
  // --------------------------------------------- equality and congruence
  struct NewEq
  {
    ENode* d_lhs;
    ENode* d_rhs;
    EqJustification d_justification;
    NewEq(ENode* lhs, ENode* rhs, const EqJustification& js)
        : d_lhs(lhs), d_rhs(rhs), d_justification(js)
    {
    }
  };

  struct NewThEq
  {
    TheoryId d_thId;
    TheoryVar d_lhs;
    TheoryVar d_rhs;
    NewThEq(TheoryId id, TheoryVar l, TheoryVar r)
        : d_thId(id), d_lhs(l), d_rhs(r)
    {
    }
  };

  struct Scope
  {
    size_t d_assignedLiteralsLim;
    size_t d_auxClausesLim;
    size_t d_justificationsLim;
    size_t d_unitsToReassertLim;
  };

  struct BaseScope
  {
    size_t d_lemmasLim;
    size_t d_simpQheadLim;
    bool d_inconsistent;
  };

  /** A unit literal that is reasserted after every backtrack. */
  struct ReplayUnit
  {
    Node d_unit;
    bool d_sign;
    bool d_relevant;
  };

  using ExprBoolPair = std::pair<Node, bool>;

  static constexpr double s_activityLimit = 1e100;
  static constexpr double s_invActivityLimit = 1e-100;

  // ----------------------------------------------------------- the E-graph
  void pushNewThEq(TheoryId th, TheoryVar lhs, TheoryVar rhs);
  void pushNewThDiseq(TheoryId th, TheoryVar lhs, TheoryVar rhs);
  void removeParentsFromCgTable(ENode* r1);
  void reinsertParentsIntoCgTable(
      ENode* r1, ENode* r2, ENode* n1, ENode* n2, EqJustification js);
  void mergeCgcGenerations(ENode* e1, uint32_t e1Generation, ENode* e2);
  void setGenerationSticky(ENode* e, uint32_t generation);
  void invertTrans(ENode* n);
  TheoryVar getClosestVar(ENode* n, TheoryId thId);
  void mergeTheoryVars(ENode* r2, ENode* r1, EqJustification js);
  void propagateBoolENodeAssignment(ENode* r1, ENode* r2, ENode* n1, ENode* n2);
  void propagateBoolENodeAssignmentCore(ENode* source, ENode* target);
  void applyStickyUpdates(ENode* e1,
                          uint32_t e1Generation,
                          ENode* e2,
                          uint32_t e2Generation);
  void restoreTheoryVars(ENode* r2, ENode* r1);

  void pushEq(ENode* lhs, ENode* rhs, const EqJustification& js)
  {
    if (lhs->getRoot() != rhs->getRoot())
    {
      d_eqPropagationQueue.push_back(NewEq(lhs, rhs, js));
    }
  }

  void pushNewCongruence(ENode* n1, ENode* n2, bool usedCommutativity)
  {
    Assert(n1->d_cg == n2);
    pushEq(n1, n2, EqJustification::mkCg(usedCommutativity));
  }

  bool addDiseq(ENode* n1, ENode* n2);
  bool isDiseqCore(ENode* n1, ENode* n2, bool checkDistinctRootValues) const;

  void assignQuantifier(TNode q);

  void setConflict(const BJustification& js, Literal notL);

  void setConflict(const BJustification& js) { setConflict(js, s_nullLiteral); }

  // ----------------------------------------------------------- the search
  void assignCore(Literal l, BJustification j, bool decision = false);
  bool bcp();
  bool propagateEqs();
  bool propagateAtoms();
  void pushNewThDiseqs(ENode* r, TheoryVar v, Theory* th);
  void propagateBoolVarENode(BoolVar v);
  void propagateRelevancy(size_t qhead);
  bool propagateTheories();
  void propagateThEqs();
  void propagateThDiseqs();
  bool canTheoriesPropagate() const;
  bool propagate();

  bool decide();
  void updatePhaseCacheCounter();
  void rescaleBoolVarActivity();
  void decayBvarActivity() { d_bvarInc *= d_params.d_invDecay; }

  void initSearch();
  void endSearch();
  LBool search();
  void incLimits();
  bool restart(LBool& status, uint32_t currLvl);
  void tick(uint32_t& counter) const;
  LBool boundedSearch();
  FinalCheckStatus finalCheck();
  void forgetPhaseOfVarsInCurrentLevel();
  virtual bool resolveConflict();
  void recordRelevancy(size_t n, const Literal* lits);
  void restoreRelevancy(size_t n, const Literal* lits);

  bool checkPreamble();
  LBool checkFinalize(LBool r);

  void assertedInconsistent();
  void initAssumptions(const std::vector<Node>& asms);
  void resetAssumptions();
  LBool mkUnsatCore(LBool result);

  // --------------------------------------------------------- backtracking
  void pushScope();
  size_t popScopeCore(size_t numScopes);
  void popScope(size_t numScopes);
  void popToSearchLvl();
  void unassignVars(size_t oldLim);
  void removeWatchLiteral(Clause* cls, size_t idx);
  void removeClsOccs(Clause* cls);
  void delClause(Clause* cls);
  void delClauses(ClauseVector& v, size_t oldSize);
  void delJustifications(JustificationVector& justifications, size_t oldLim);
  bool isUnitClause(const Clause* c) const;
  bool isEmptyClause(const Clause* c) const;
  void cacheGeneration(uint32_t newScopeLvl);
  void cacheGeneration(const Clause* cls, uint32_t newScopeLvl);
  void cacheGeneration(size_t numLits,
                       const Literal* lits,
                       uint32_t newScopeLvl);
  void cacheGeneration(TNode n, uint32_t newScopeLvl);
  void resetCacheGeneration();
  void reinitClauses(size_t numScopes, size_t numBoolVars);
  void reassertUnits(size_t unitsToReassertLim);
  void removeWatch(BoolVar v);

  // ------------------------------------------------- clause simplification
  bool simplifyClause(Clause& cls);
  size_t simplifyClauses(ClauseVector& clauses, size_t startingAt);
  void simplifyClauses();
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
  void delInactiveLemmas();
  void delInactiveLemmas1();
  void delInactiveLemmas2();
  bool moreThanKUnassignedLiterals(Clause* cls, size_t k);

  // -------------------------------------------------------- internalization
  void updateGeneration(ENode* n);
  void updateGeneration(TNode e)
  {
    if (isApp(e) && eInternalized(e))
    {
      updateGeneration(getENode(e));
    }
  }
  void tsVisitChild(TNode n,
                    bool gateCtx,
                    std::vector<ExprBoolPair>& todo,
                    bool& visited);
  bool tsVisitChildren(TNode n, bool gateCtx, std::vector<ExprBoolPair>& todo);
  bool shouldInternalizeRec(TNode e) const;
  void topSortExpr(const Node* exprs,
                   size_t numExprs,
                   std::vector<ExprBoolPair>& sortedExprs);
  void internalizeRec(TNode n, bool gateCtx);
  void internalizeDeep(TNode n);
  void internalizeDeep(const Node* exprs, size_t numExprs);
  void internalizeAssertion(TNode n, uint32_t generation);
  void assertDefault(TNode n);
  void assertDistinct(TNode n);
  void internalizeFormula(TNode n, bool gateCtx);
  void internalizeEq(TNode n, bool gateCtx);
  void internalizeDistinct(TNode n, bool gateCtx);
  bool internalizeTheoryAtom(TNode n, bool gateCtx);
  void internalizeQuantifier(TNode q, bool gateCtx);
  void internalizeFormulaCore(TNode n, bool gateCtx);
  void setMergeTf(ENode* n, BoolVar v, bool isNewVar);
  void internalizeTerm(TNode n);
  void internalizeIteTerm(TNode n);
  bool internalizeTheoryTerm(TNode n);
  void internalizeUninterpreted(TNode n);
  /** Check that some plugin can reason about n's theory. */
  void checkTheorySupported(TNode n);
  void undoMkBoolVar();
  void undoMkENode();
  void applySortCnstr(TNode term, ENode* e);
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
  bool trackOccs() const { return d_params.d_phaseSelection == PS_OCCURRENCE; }
  void decRef(Literal l);
  void incRef(Literal l);
  void removeLitOccs(const Clause& cls, size_t numBoolVars);
  void addLitOccs(const Clause& cls);
  void addScores(size_t n, const Literal* lits);

  void init();
  void flush();

  // ------------------------------------------------------------- the fields
  Params& d_params;
  uint32_t d_relevancyLvl;
  Region d_region;
  QuantifierNormalizer d_normalizer;
  ConnectiveNormalizer d_connNormalizer;
  AssertionRewriter d_assertionRewriter;
  Nnf d_nnf;
  NgPushAppIte d_ngPushAppIte;
  std::unique_ptr<Cvc5Bridge> d_cvc5Bridge;
  PatternInference d_patternInference;
  /** true if the input uses a construct that is not supported */
  bool d_unsupported = false;
  std::unique_ptr<QuantifierManager> d_qmanager;
  std::unique_ptr<RelevancyPropagator> d_relevancyPropagator;
  RandomGen d_random;
  bool d_flushing;
  FingerprintSet d_fingerprints;

  /** The formulas asserted into this context, and how far we internalized. */
  std::vector<Node> d_assertedFormulas;
  size_t d_assertedFormulasQhead;
  bool d_assertedInconsistent;
  bool d_hasQuantifiers;
  bool d_internalizingAssertions;
  bool d_interrupted;

  /** The Boolean expressions already internalized. */
  std::vector<Node> d_bInternalizedStack;
  /** The expressions already internalized as enodes. */
  std::vector<Node> d_eInternalizedStack;

  JustificationVector d_justifications;

  /** A circular counter used to give the theories a fair final check. */
  size_t d_finalCheckIdx;

  std::vector<double> d_litScores[2];
  std::vector<uint64_t> d_birthdate;

  // ------------------------------------- equality and uninterpreted functions
  ENode* d_trueENode;
  ENode* d_falseENode;
  /** Maps the id of a term to its enode. */
  App2ENode d_app2ENode;
  ENodeVector d_enodes;
  /** Maps a theory id to its plugin. */
  std::vector<Theory*> d_theories;
  /** The registered theories, for fast traversal. */
  std::vector<Theory*> d_theorySet;
  /** Maps a declaration id to the enodes with that declaration. */
  std::vector<ENodeVector> d_decl2ENodes;
  std::unordered_map<TNode, uint32_t> d_declIds;
  ENodeVector d_emptyVector;
  CgTable d_cgTable;
  std::unordered_map<ENode*, uint32_t> d_stickyGenerationUpdates;
  /**
   * A temporary cache of parent generations, held between
   * removeParentsFromCgTable and reinsertParentsIntoCgTable.
   */
  std::vector<std::pair<ENode*, uint32_t>> d_r1ParentGenerations;
  std::vector<NewEq> d_eqPropagationQueue;
  std::vector<NewThEq> d_thEqPropagationQueue;
  std::vector<NewThEq> d_thDiseqPropagationQueue;
  /** An auxiliary enode used to find congruent equality atoms. */
  ENode* d_isDiseqTmp;
  Node d_isDiseqTmpExpr;
  TmpENode d_tmpENode;

  // ------------------------------------------------------- the Boolean engine
  /** Maps the id of an expression to its Boolean variable. */
  std::vector<BoolVar> d_expr2BoolVar;
  /** Maps a Boolean variable to its expression. */
  std::vector<Node> d_boolVar2Expr;
  /** Maps a literal index to its assignment. */
  std::vector<int8_t> d_assignment;
  /** The watch list of each literal. */
  std::vector<WatchList> d_watches;
  /** The occurrence count of each literal. */
  std::vector<uint32_t> d_litOccs;
  std::vector<BoolVarData> d_bdata;
  std::vector<double> d_activity;
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

  /*
    A conflict is usually a single justification, i.e. a justification for
    false. If d_notL is not the null literal then d_conflict justifies l, and
    the conflict is the union of d_notL and d_conflict.
  */
  BJustification d_conflict;
  Literal d_notL;
  std::unique_ptr<ConflictResolution> d_conflictResolution;

  LiteralVector d_atomPropagationQueue;

  std::unordered_map<TNode, uint32_t> d_cachedGeneration;
  std::unordered_set<TNode> d_cacheGenerationVisited;
  DynAckManager d_dynAckManager;

  // --------------------------------------------------------- model generation
  Node d_model;
  std::string d_unknown;

  // ------------------------------------------------------ unsat core support
  LiteralVector d_assumptions;
  std::unordered_map<size_t, Node> d_literal2Assumption;
  std::vector<Node> d_unsatCore;

  // -------------------------------------------------------- theory case split
  UIntSet d_allThCaseSplitLiterals;
  std::vector<LiteralVector> d_thCaseSplitSets;
  std::unordered_map<size_t, std::vector<LiteralVector>>
      d_literal2CaseSplitSets;

  // ------------------------------------------------------------ backtracking
  TrailStack d_trailStack;
  uint32_t d_scopeLvl;
  uint32_t d_baseLvl;
  /**
   * Greater than d_baseLvl when assumptions are used, and equal to it
   * otherwise.
   */
  uint32_t d_searchLvl;
  std::vector<Scope> d_scopes;
  std::vector<BaseScope> d_baseScopes;

  /** A temporary variable used during internalization. */
  uint32_t d_generation;

  // ------------------------------------------------------------------ engine
  LBool d_lastSearchResult;
  Failure d_lastSearchFailure;
  /** The theories that failed to produce a model. */
  std::vector<Theory*> d_incompleteTheories;
  bool d_searching;
  bool d_searchFinalized;
  bool d_setupDone;
  uint64_t d_numConflicts;
  uint64_t d_numConflictsSinceRestart;
  uint64_t d_numConflictsSinceLemmaGc;
  uint64_t d_numRestarts;
  uint64_t d_numSimplifications;
  uint64_t d_restartThreshold;
  uint64_t d_restartOuterThreshold;
  uint32_t d_lubyIdx;
  double d_agility;
  uint64_t d_lemmaGcThreshold;
  bool d_hasCaseSplit;
  /** The theories that could not confirm the assignment extends to a model. */
  std::set<int32_t> d_modelUnsoundTheories;
  std::vector<bool> d_relevantConflictLiterals;

  /** Scratch space for the topological sort used by internalizeDeep. */
  std::vector<ExprBoolPair> d_tsTodo;
  std::vector<char> d_tcolors;
  std::vector<char> d_fcolors;

  /** The trail object that undoes mkBoolVar. */
  class MkBoolVarTrail : public Trail
  {
   public:
    MkBoolVarTrail(SmtContext& ctx) : d_ctx(ctx) {}
    void undo() override { d_ctx.undoMkBoolVar(); }

   private:
    SmtContext& d_ctx;
  };
  MkBoolVarTrail d_mkBoolVarTrail;

  /** The trail object that undoes mkENode. */
  class MkENodeTrail : public Trail
  {
   public:
    MkENodeTrail(SmtContext& ctx) : d_ctx(ctx) {}
    void undo() override { d_ctx.undoMkENode(); }

   private:
    SmtContext& d_ctx;
  };
  MkENodeTrail d_mkENodeTrail;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__SMT_CONTEXT_H */
