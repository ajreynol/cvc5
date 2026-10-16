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
#include <functional>
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
#include "z3/explainer.h"
#include "z3/justification.h"
#include "z3/nnf.h"
#include "z3/params.h"
#include "z3/pattern_inference.h"
#include "z3/prop_core.h"
#include "z3/push_app_ite.h"
#include "z3/quantifier_manager.h"
#include "z3/quantifier_services.h"
#include "z3/relevancy.h"
#include "z3/statistics.h"
#include "z3/theory.h"
#include "z3/theory_status.h"
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

/**
 * The theory side of the ported core; PropCore is the propositional side.
 * The quantifier stack reaches it only through QuantifierServices.
 */
class SmtContext final : protected EnvObj, public QuantifierServices
{
  friend class ModelGenerator;
  friend class ConflictResolution;
  friend class DynAckManager;

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
  void setupContext(bool useStaticFeatures);

  void setupComponents();

  ConfigMode getConfigMode(bool useStaticFeatures) const;

  // ---------------------------------------------------------- assertions
  //
  // The asserted formulas, the checks and user scopes are driven by the
  // propositional side, PropCore; Z3PropEngine calls it. The methods below
  // forward to it for the theory side.

  /** Assert a (prepared) formula. */
  void assertFormula(TNode e) { d_prop.assertFormula(e); }

  /** A development hook: dump the assigned relevant literals to a file. */
  void dumpCandidateModel(const char* path);

  /** Write what the core was given, as a parsable benchmark. */
  void dumpAssertions(const char* path);

  /** A development hook: check the candidate model with a cvc5 subsolver. */
  void checkCandidateModel();

  /** Internalize the assertions that have not been internalized yet. */
  void internalizeAssertions() { d_prop.internalizeAssertions(); }

  size_t getNumAssertedFormulas() const
  {
    return d_prop.getNumAssertedFormulas();
  }

  TNode getAssertedFormula(size_t idx) const
  {
    return d_prop.getAssertedFormula(idx);
  }

  /**
   * Internalize the asserted formula n, of the given generation: its subterms,
   * then its Boolean structure through PropCore::assertRoot.
   */
  void internalizeAssertion(TNode n, uint32_t generation);

  /**
   * As internalizeAssertion, but through PropCore::assertPermanentLemma, whose
   * result is returned.
   */
  bool internalizePermanentLemma(TNode n, uint32_t generation);

  // -------------------------------------------------------------- search
  Failure getLastSearchFailure() const { return d_prop.getLastSearchFailure(); }

  // ------------------------------------- the scheduling and backtracking
  //                                       contract, called by PropCore
  /**
   * Propagate on the theory side, after Boolean propagation and relevancy
   * have saturated: the assigned atoms, the equalities, the theories and the
   * quantifiers, in that order. Returns false on a conflict.
   */
  bool theoryPropagate();

  /** Whether the theory side has propagation work pending. */
  bool hasPendingTheoryWork() const;

  /** Called at the start of a search. */
  void initSearchEh();

  /**
   * The final check, when every Boolean variable is assigned. If the theory
   * side gives up for a known reason, failure is set to it, and otherwise to
   * OK.
   */
  FinalCheckStatus finalCheck(Failure& failure);

  /** Called on a restart, after backtracking to the search level. */
  void restartEh();

  /**
   * Whether a satisfying assignment of the quantifier-free part is a model.
   * SAT if there are no quantifiers to check.
   */
  QuantifierManager::CheckModelResult checkModel();

  /** Called after each conflict is resolved, when the search continues. */
  void notifyConflictResolved();

  /** Drop the pending propagations, when a conflict is found. */
  void clearPropagationQueues();

  /** Push a scope of the theory side, after the propositional side's. */
  void pushTheoryScope();

  /**
   * Pop numScopes scopes of the quantifier manager, before the Boolean
   * variables are unassigned.
   */
  void popTheoryScopeBegin(size_t numScopes);

  /**
   * Pop numScopes scopes of the rest of the theory side, down to newLvl,
   * after the Boolean variables are unassigned: the trail, the theories, the
   * justifications, the propagation queues and the region.
   */
  void popTheoryScopeEnd(size_t numScopes, uint32_t newLvl);

  void resetCacheGeneration();

  Explainer& getExplainer() { return d_explainer; }

  void setReasonUnknown(const std::string& msg) override
  {
    d_prop.setReasonUnknown(msg);
  }

  /** Print the quantifier profile, if requested, when a check finishes. */
  void reportQuantifierProfile();

  /**
   * Whether an assignment that satisfies the Boolean abstraction may be
   * reported as a model; see TheoryStatus::canConfirmModel.
   */
  bool canConfirmModel(std::string& reason) const;

  std::ostream& printLastFailure(std::ostream& out) const;

  // ----------------------------------------------------------- accessors
  Params& getParams() override { return d_params; }

  const Params& getParams() const { return d_params; }

  Statistics& getStats() override { return d_stats; }

  Region& getRegion() override { return d_region; }

  bool relevancy() const override { return d_prop.relevancy(); }

  uint32_t relevancyLvl() const { return d_prop.relevancyLvl(); }

  ENode* getENode(TNode n) const override
  {
    Assert(eInternalized(n));
    return d_app2ENode[n.getId()];
  }

  /** Like getENode, but returns null if n is not internalized. */
  ENode* findENode(TNode n) const
  {
    return getx(d_app2ENode, n.getId(), static_cast<ENode*>(nullptr));
  }

  // ------------------------------------- the Boolean search, see PropCore
  //
  // The methods below forward to the propositional side, d_prop. They are
  // the Boolean API that the theory side, the theory plugins and the
  // quantifier engine use.

  /** The propositional side. */
  PropCore& getPropCore() { return d_prop; }

  const PropCore& getPropCore() const { return d_prop; }

  BoolVar getBoolVar(TNode n) const { return d_prop.getBoolVar(n); }

  BoolVar getBoolVar(const ENode* n) const { return getBoolVar(n->getExpr()); }

  BoolVar getBoolVarOfId(size_t id) const { return d_prop.getBoolVarOfId(id); }

  const ClauseVector& getLemmas() const { return d_prop.getLemmas(); }

  Literal getLiteral(TNode n) const { return d_prop.getLiteral(n); }

  bool hasENode(BoolVar v) const { return getBdata(v).isENode(); }

  ENode* boolVar2ENode(BoolVar v) const
  {
    Assert(getBdata(v).isENode());
    return d_app2ENode[boolVar2Expr(v).getId()];
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

  size_t getNumBoolVars() const { return d_prop.getNumBoolVars(); }

  BoolVarData& getBdata(BoolVar v) { return d_prop.getBdata(v); }

  const BoolVarData& getBdata(BoolVar v) const { return d_prop.getBdata(v); }

  LBool getAssignment(Literal l) const { return d_prop.getAssignment(l); }

  LBool getAssignment(BoolVar v) const { return d_prop.getAssignment(v); }

  const LiteralVector& assignedLiterals() const
  {
    return d_prop.assignedLiterals();
  }

  LBool getAssignment(TNode n) const override
  {
    return d_prop.getAssignment(n);
  }

  LBool getAssignment(ENode* n) const;

  void setRandomSeed(uint32_t s) { d_random.setSeed(s); }

  int getRandomValue() { return d_random(); }

  bool isSearching() const { return d_prop.isSearching(); }

  uint64_t getNumAssignments() const { return d_stats.d_numAssignments; }

  uint64_t getBirthdate(BoolVar v) const { return d_prop.getBirthdate(v); }

  /** The scope level at which v was assigned. */
  uint32_t getAssignLevel(BoolVar v) const { return d_prop.getAssignLevel(v); }

  uint32_t getAssignLevel(Literal l) const { return d_prop.getAssignLevel(l); }

  /** The scope level at which v was internalized. */
  uint32_t getInternLevel(BoolVar v) const { return d_prop.getInternLevel(v); }

  Theory* getTheory(TheoryId thId) const
  {
    return thId == s_nullTheoryId ? nullptr : d_theories[thId];
  }

  const std::vector<Theory*>& theories() const { return d_theorySet; }

  uint32_t getScopeLevel() const override { return d_prop.getScopeLevel(); }

  uint32_t getBaseLevel() const { return d_prop.getBaseLevel(); }

  bool atBaseLevel() const { return d_prop.atBaseLevel(); }

  uint32_t getSearchLevel() const { return d_prop.getSearchLevel(); }

  TNode boolVar2Expr(BoolVar v) const { return d_prop.boolVar2Expr(v); }

  bool isTrue(const ENode* n) const { return n == d_trueENode; }

  bool isFalse(const ENode* n) const { return n == d_falseENode; }

  size_t getNumENodesOf(TNode decl) const override
  {
    uint32_t id = getDeclIdOption(decl);
    return id < d_decl2ENodes.size() ? d_decl2ENodes[id].size() : 0;
  }

  const ENodeVector& enodesOf(TNode decl) const override
  {
    uint32_t id = getDeclIdOption(decl);
    return id < d_decl2ENodes.size() ? d_decl2ENodes[id] : d_emptyVector;
  }

  const ENodeVector& enodes() const override { return d_enodes; }

  uint32_t getGeneration(ENode* e) const override
  {
    // Patterns with equalities are not supported, so there is no need to
    // track the generation of equality nodes.
    if (e->isEq())
    {
      return 0;
    }
    return getCgRoot(e)->d_generation;
  }

  uint32_t getMaxGeneration(size_t numENodes, ENode* const* enodes) override
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
  bool hasQuantifiers() const { return d_prop.hasQuantifiers(); }

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

  TrailStack& getTrailStack() override { return d_trailStack; }

  // ------------------------------------------------------ internalization
  bool bInternalized(TNode n) const override { return d_prop.bInternalized(n); }

  bool litInternalized(TNode n) const override
  {
    return d_prop.litInternalized(n);
  }

  bool eInternalized(TNode n) const override
  {
    return getx(d_app2ENode, n.getId(), static_cast<ENode*>(nullptr))
           != nullptr;
  }

  size_t getNumEInternalized() const { return d_eInternalizedStack.size(); }

  TNode getEInternalized(size_t idx) const { return d_eInternalizedStack[idx]; }

  /** The canonicalizer for quantifiers; see z3/ast.h. */
  QuantifierNormalizer& getNormalizer() { return d_normalizer; }

  PatternInference& getPatternInference() { return d_patternInference; }

  ConnectiveNormalizer& getConnectiveNormalizer() { return d_connNormalizer; }

  AssertionRewriter& getAssertionRewriter() { return d_assertionRewriter; }

  Nnf& getNnf() { return d_nnf; }

  /** Z3's ng_lift_ite step; see z3/push_app_ite.h. */
  NgPushAppIte& getNgPushAppIte() { return d_ngPushAppIte; }

  /**
   * The preprocessing of cvc5's own theories, when they fill theory slots
   * next to the port's (--z3-slots other than all): it maps a formula to the
   * form cvc5's theories take, adding to defs the definitions of the skolems
   * it introduces. The input (AssertionPreparation) and the instances
   * (internalizeInstance) go through it before the core asserts them and
   * hands them to cvc5, so that both see the same atoms.
   */
  using Cvc5Preprocessor = std::function<Node(TNode, std::vector<Node>&)>;
  void setCvc5Preprocessor(Cvc5Preprocessor p)
  {
    d_cvc5Preprocessor = std::move(p);
  }
  /** The preprocessing of cvc5's theories, or null if there is none. */
  const Cvc5Preprocessor& getCvc5Preprocessor() const
  {
    return d_cvc5Preprocessor;
  }

  /**
   * Merge the classes of a and b, which must be internalized as terms, since
   * cvc5's theories made them equal (--no-z3-shadow-plugins). The merge is
   * queued for the next propagation. The core cannot explain it.
   */
  void assumeExternalEq(TNode a, TNode b)
  {
    pushEq(getENode(a), getENode(b), EqJustification(&d_externalJustification));
  }
  /** Note that an explanation went through an equality of cvc5's theories. */
  void noteUnexplainable() { d_unexplainable = true; }
  /**
   * Whether an explanation went through an equality of cvc5's theories since
   * the last call, which makes it incomplete.
   */
  bool takeUnexplainable()
  {
    bool u = d_unexplainable;
    d_unexplainable = false;
    return u;
  }

  /** The environment of the enclosing cvc5 solver. */
  const Env& getEnv() const override { return d_env; }

  /** The shared state of the bridges to cvc5's own theory solvers. */
  Cvc5Bridge& getCvc5Bridge();

  /**
   * Record that the input uses a construct this port does not support, so
   * that the search answers "unknown" instead of guessing.
   */
  void markUnsupported() { d_theoryStatus.markUnsupported(); }

  bool isUnsupported() const { return d_theoryStatus.isUnsupported(); }

  /**
   * Internalize the body of a quantifier instance, after renormalizing its
   * variables. The instance is asserted at the current scope, or with
   * --z3-qi-permanent as a lemma that survives backtracking. Returns true in
   * the latter case, and then sets root to the formula asserted, for
   * reactivateInstance.
   */
  bool internalizeInstance(TNode body,
                           uint32_t generation,
                           Node& root) override;

  /**
   * Make the permanent instance root a root again in the current scope, when
   * matching finds it again (--z3-qi-permanent-local).
   */
  void reactivateInstance(TNode root) override
  {
    d_prop.reactivatePermanentRoot(root);
  }

  void ensureInternalized(TNode e);

  void internalize(TNode n, bool gateCtx);
  void internalize(const Node* exprs, size_t numExprs, bool gateCtx);
  void internalize(TNode n, bool gateCtx, uint32_t generation) override;

  ENode* nonGroundInternalize(TNode e);

  Clause* mkClause(size_t numLits,
                   Literal* lits,
                   Justification* j,
                   ClauseKind k = CLS_AUX,
                   ClauseDelEh* delEh = nullptr)
  {
    return d_prop.mkClause(numLits, lits, j, k, delEh);
  }

  void mkClause(Literal l1, Literal l2, Justification* j)
  {
    d_prop.mkClause(l1, l2, j);
  }

  void mkClause(Literal l1, Literal l2, Literal l3, Justification* j)
  {
    d_prop.mkClause(l1, l2, l3, j);
  }

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

  // ---------------------------------------------------- trail callbacks
  /** Undo an addEq; invoked from the trail. */
  void undoAddEq(ENode* r1, ENode* n1, size_t r2NumParents);

  /** Undo a congruence class generation merge; invoked from the trail. */
  void undoMergeCgcGenerations(ENode* e1,
                               uint32_t e1Generation,
                               ENode* e2,
                               uint32_t e2Generation);

  BoolVar mkBoolVar(TNode n) { return d_prop.mkBoolVar(n); }

  /**
   * Make the Boolean variable of atom, an atom of the theory tid, which is
   * notified of its assignments. If hasENode, the enode of atom has already
   * been made, and is merged with true or false when the variable is
   * assigned. This is how a theory plugin registers an atom.
   */
  BoolVar mkTheoryAtomVar(TNode atom, TheoryId tid, bool hasENode = false);

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

  /** Keep j, which is not in the region, until its scope is popped. */
  void addJustification(Justification* j) { d_justifications.push_back(j); }

  /** Hand an assigned atom to the theory side; see propagateAtoms. */
  void enqueueAtom(Literal l) { d_atomPropagationQueue.push_back(l); }

  /** Called when the Boolean variable of n is deleted on backtracking. */
  void notifyBoolVarDeleted(TNode n);

  /**
   * Cache the generation of the enodes and quantifiers in n that backtracking
   * to newScopeLvl deletes, so that they are recreated with it.
   */
  void cacheGeneration(TNode n, uint32_t newScopeLvl);

  void mkGateClause(size_t numLits, Literal* lits)
  {
    d_prop.mkGateClause(numLits, lits);
  }
  void mkGateClause(Literal l1, Literal l2) { d_prop.mkGateClause(l1, l2); }
  void mkGateClause(Literal l1, Literal l2, Literal l3)
  {
    d_prop.mkGateClause(l1, l2, l3);
  }
  void mkGateClause(Literal l1, Literal l2, Literal l3, Literal l4)
  {
    d_prop.mkGateClause(l1, l2, l3, l4);
  }

  /**
   * Internalize n, a subterm of an assertion, in the given context; see
   * PropCore::assertRoot.
   */
  void internalizeRec(TNode n, bool gateCtx);

  void setEnodeFlag(BoolVar v, bool isNewVar);

  // ------------------------------------------------------------- engine
  void assign(Literal l, const BJustification& j, bool decision = false)
  {
    d_prop.assign(l, j, decision);
  }

  void assign(Literal l, Justification* j, bool decision = false)
  {
    d_prop.assign(l, j, decision);
  }

  void setTrueFirstFlag(BoolVar v) { d_prop.setTrueFirstFlag(v); }

  bool tryTrueFirst(BoolVar v) const { return d_prop.tryTrueFirst(v); }

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
  void forcePhase(BoolVar v, bool phase) { d_prop.forcePhase(v, phase); }

  void forcePhase(Literal l) { d_prop.forcePhase(l); }

  void setGlobalGeneration(uint32_t generation) { d_generation = generation; }

  void addEq(ENode* n1, ENode* n2, EqJustification js);

  void setConflict(Justification* js) { d_prop.setConflict(js); }

  bool inconsistent() const override { return d_prop.inconsistent(); }

  uint64_t getNumConflicts() const { return d_prop.getNumConflicts(); }

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

  bool isDiseq(ENode* n1, ENode* n2) const override;

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

  /**
   * Whether v is the variable of an equality atom whose sides are known to be
   * disequal, as isExtDiseq with depth 2 decides. For the lookahead of the
   * relevancy case split queue (d_lookaheadDiseq), through PropCore.
   */
  bool isExtDiseqAtom(BoolVar v);

  /**
   * Tell the theory of the atom of v that conflict resolution marked v
   * (Theory::conflictResolutionEh). Called by ConflictResolution through
   * PropCore.
   */
  void conflictResolutionEh(BoolVar v);

  /** An enode congruent to decl(args), or null if there is none. */
  ENode* getENodeEqTo(TNode decl,
                      bool commutative,
                      size_t numArgs,
                      ENode* const* args) override;

  bool canPropagate() const override { return d_prop.canPropagate(); }

  // ------------------------------------------------------------ relevancy
  //
  // Relevancy belongs to the propositional side; see PropCore. The methods
  // below forward to it.

  /**
   * Notify the quantifier manager and the theories that n became relevant;
   * called by PropCore::relevantEh.
   */
  void relevantEh(TNode n);

  bool isRelevantCore(TNode n) const { return d_prop.isRelevantCore(n); }

  bool isRelevant(TNode n) const override { return d_prop.isRelevant(n); }

  bool isRelevant(ENode* n) const { return isRelevant(n->getExpr()); }

  bool isRelevant(BoolVar v) const { return d_prop.isRelevant(v); }

  bool isRelevant(Literal l) const { return d_prop.isRelevant(l); }

  bool isRelevantCore(Literal l) const { return d_prop.isRelevantCore(l); }

  /**
   * Whether E-matching considers n: n is relevant, or relevancy does not
   * restrict matching (--no-z3-relevancy-match).
   */
  bool isRelevantForMatching(TNode n) const
  {
    return !d_params.d_relevancyMatch || isRelevant(n);
  }

  bool isRelevantForMatching(ENode* n) const override
  {
    return !d_params.d_relevancyMatch || isRelevant(n);
  }

  /**
   * Whether the instance checkers consider n: n is relevant, or relevancy
   * does not restrict them (--no-z3-relevancy-check).
   */
  bool isRelevantForChecking(TNode n) const override
  {
    return !d_params.d_relevancyCheck || isRelevant(n);
  }

  bool isRelevantForChecking(ENode* n) const override
  {
    return !d_params.d_relevancyCheck || isRelevant(n);
  }

  void markAsRelevant(TNode n) { d_prop.markAsRelevant(n); }

  void markAsRelevant(ENode* n) override { markAsRelevant(n->getExpr()); }

  void markAsRelevant(BoolVar v) { d_prop.markAsRelevant(v); }

  void markAsRelevant(Literal l) { d_prop.markAsRelevant(l); }

  template <typename Eh>
  RelevancyEh* mkRelevancyEh(const Eh& eh)
  {
    return d_prop.mkRelevancyEh(eh);
  }

  void addRelevancyEh(TNode source, RelevancyEh* eh)
  {
    d_prop.addRelevancyEh(source, eh);
  }

  void addRelevancyDependency(TNode source, TNode target)
  {
    d_prop.addRelevancyDependency(source, target);
  }

  void addRelWatch(Literal l, RelevancyEh* eh) { d_prop.addRelWatch(l, eh); }

  void addRelWatch(Literal l, TNode n) { d_prop.addRelWatch(l, n); }

  // -------------------------------------------------- value extraction
  bool getValue(ENode* n, Node& value) override;

  /**
   * Rewrite a quantifier instance before it is internalized. Z3 applies its
   * th_rewriter here; this port uses cvc5's rewriter.
   */
  Node rewriteInstance(TNode n) const override { return rewrite(n); }

  /**
   * A dense id for a declaration, created on demand. This is the counterpart
   * of Z3's func_decl::get_small_id, which the E-matching engine uses to index
   * its tables by function symbol.
   */
  uint32_t getDeclId(TNode decl) override;
  /** The dense id of decl, or UINT32_MAX if it has none yet. */
  uint32_t getDeclIdOption(TNode decl) const override;

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
  void markModelUnsound(TheoryId tid) { d_theoryStatus.markModelUnsound(tid); }

  /** True if any theory was internalized without a plugin. */
  bool isModelUnsound() const { return d_theoryStatus.isModelUnsound(); }

  bool resourceLimitsExceeded() override
  {
    return d_prop.resourceLimitsExceeded();
  }

  bool getCancelFlag() override { return d_prop.getCancelFlag(); }

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

  using ExprBoolPair = std::pair<Node, bool>;

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

  void setConflict(const BJustification& js, Literal notL)
  {
    d_prop.setConflict(js, notL);
  }

  void setConflict(const BJustification& js) { d_prop.setConflict(js); }

  // ----------------------------------------------------------- the search
  bool propagateEqs();
  bool propagateAtoms();
  void pushNewThDiseqs(ENode* r, TheoryVar v, Theory* th);
  void propagateBoolVarENode(BoolVar v);
  bool propagateTheories();
  void propagateThEqs();
  void propagateThDiseqs();
  bool canTheoriesPropagate() const;

  // --------------------------------------------------------- backtracking
  void delJustifications(JustificationVector& justifications, size_t oldLim);

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
  void internalizeDeep(TNode n);
  void internalizeDeep(const Node* exprs, size_t numExprs);
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
  void undoMkENode();
  void applySortCnstr(TNode term, ENode* e);

  void init();
  void flush();

  // ------------------------------------------------------------- the fields
  Params& d_params;
  /**
   * The propositional side: the Boolean search state. It refers to d_params
   * and d_stats, so it is declared after them.
   */
  PropCore d_prop;
  Region d_region;
  QuantifierNormalizer d_normalizer;
  ConnectiveNormalizer d_connNormalizer;
  AssertionRewriter d_assertionRewriter;
  Nnf d_nnf;
  NgPushAppIte d_ngPushAppIte;
  /** See setCvc5Preprocessor. */
  Cvc5Preprocessor d_cvc5Preprocessor;
  /** The justification of the equalities of cvc5's theories. */
  ExternalEqJustification d_externalJustification;
  /** See takeUnexplainable. */
  bool d_unexplainable = false;
  std::unique_ptr<Cvc5Bridge> d_cvc5Bridge;
  PatternInference d_patternInference;
  /**
   * What the theory side knows about whether a satisfying assignment is a
   * model, which checkFinalize consults.
   */
  TheoryStatus d_theoryStatus;
  std::unique_ptr<QuantifierManager> d_qmanager;
  RandomGen d_random;

  /** The expressions already internalized as enodes. */
  std::vector<Node> d_eInternalizedStack;

  JustificationVector d_justifications;
  /** The size of d_justifications when each open scope was pushed. */
  std::vector<size_t> d_justificationsLims;

  /** A circular counter used to give the theories a fair final check. */
  size_t d_finalCheckIdx;

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

  LiteralVector d_atomPropagationQueue;

  std::unordered_map<TNode, uint32_t> d_cachedGeneration;
  /**
   * Under cvc5's prop engine, the generation each term and quantifier had
   * when it was first internalized. cvc5 keeps the clauses whose atoms this
   * side deletes on backtracking, and asserts those atoms again later; they
   * are then internalized on demand, outside the reinitialization that
   * d_cachedGeneration serves, and take their generation from here.
   */
  std::unordered_map<Node, uint32_t> d_hostGeneration;
  /** The generation of n: cached, recorded under cvc5, or the current one. */
  uint32_t generationOf(TNode n);
  std::unordered_set<TNode> d_cacheGenerationVisited;
  DynAckManager d_dynAckManager;
  /**
   * The explanation of justifications and equalities for conflict
   * resolution. It reports the congruences and equalities it uses to
   * d_dynAckManager, so it is declared after it.
   */
  Explainer d_explainer;

  // ------------------------------------------------------------ backtracking
  TrailStack d_trailStack;

  /** A temporary variable used during internalization. */
  uint32_t d_generation;

  // ------------------------------------------------------------------ engine
  bool d_setupDone;

  /** Scratch space for the topological sort used by internalizeDeep. */
  std::vector<ExprBoolPair> d_tsTodo;
  std::vector<char> d_tcolors;
  std::vector<char> d_fcolors;

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
