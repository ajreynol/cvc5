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
 * The coordinator of the core: it owns and drives the Boolean side (PropCore),
 * the E-graph (EGraph) and the quantifiers (QuantifierManager), internalizes
 * the input and the instances into the first two, runs the propagation
 * fixpoint and the scopes, and is the boundary with cvc5. The ground
 * reasoning is cvc5's theories', whose equalities reach the E-graph through
 * the master equality engine (notifyMasterMerge).
 *
 * Of Z3's context, only what E-matching and quantifier instantiation need
 * is ported: not its search (decisions, conflict resolution, restarts, lemma
 * garbage collection), its theory plugins, proof production, or Z3's
 * asserted_formulas preprocessing pipeline (cvc5's Preprocessor is used
 * instead).
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__QUANTIFIERS__SMT_CONTEXT_H
#define CVC5__Z3__QUANTIFIERS__SMT_CONTEXT_H

#include <memory>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "context/cdhashmap.h"
#include "context/cdo.h"
#include "context/context.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/decision_strategy.h"
#include "theory/incomplete_id.h"
#include "theory/inference_id.h"
#include "theory/lemma_property.h"
#include "theory/theory.h"
#include "z3/quantifiers/egraph.h"
#include "z3/quantifiers/enode.h"
#include "z3/quantifiers/quantifier_manager.h"
#include "z3/relevancy/bool_var_data.h"
#include "z3/relevancy/clause.h"
#include "z3/relevancy/prop_core.h"
#include "z3/relevancy/relevancy.h"
#include "z3/relevancy/watch_list.h"
#include "z3/util/ast.h"
#include "z3/util/literal.h"
#include "z3/util/statistics.h"
#include "z3/util/trail.h"

namespace cvc5::internal {

class TheoryEngine;

namespace theory {
class TheoryState;
namespace eq {
class EqualityEngine;
}
namespace quantifiers {
class QuantifiersInferenceManager;
}
}  // namespace theory

namespace z3 {

class LemmaProofGenerator;
class QuantifierManager;
class RelevancyTracker;

/**
 * The ported core: the coordinator of the Boolean side (PropCore), the E-graph
 * (EGraph) and the quantifiers (QuantifierManager), and the boundary with
 * cvc5.
 *
 * It implements the search contract of cvc5's prop engine (preregistration,
 * facts and checks) over PropCore, which mirrors the assignment of the atoms
 * (see setupSearch). Its scopes follow the SAT context (syncLevel).
 *
 * The core is a shadow of the ground state of cvc5's theories, made from a
 * copy of every fact: it sends instances, conflicts and splits as lemmas,
 * which need no explanation, and reports no propagations, and the formulas
 * it asserts go through cvc5's preprocessing first.
 */
class SmtContext final : protected EnvObj
{
 public:
  /** The search statistics. Public, as in Z3. */
  Statistics d_stats;

  /**
   * Lemmas go through qim, the inference manager of the quantifiers theory,
   * and the core follows the prop engine of te.
   */
  SmtContext(Env& env,
             theory::quantifiers::QuantifiersInferenceManager& qim,
             TheoryEngine* te);
  ~SmtContext();

  SmtContext(const SmtContext&) = delete;
  SmtContext& operator=(const SmtContext&) = delete;

  // -------------------------------------------- the boundary with cvc5

  /**
   * Assert the input formulas, cvc5's preprocessed assertions, to the core,
   * before cvc5 converts them.
   */
  void assertInput(const std::vector<Node>& assertions);
  /** cvc5 registered the atom. */
  void preRegister(TNode atom);
  /** cvc5 asserted the literal; see RelevancyTracker. */
  void assertFact(TNode literal);
  /**
   * Give the core the literals asserted since the last check, while state is
   * not in conflict, then propagate, and at full effort run the final check.
   */
  void check(theory::Theory::Effort effort, const theory::TheoryState& state);
  /**
   * Set up the propositional side, once, and take the merges of the master
   * equality engine.
   */
  void presolve(theory::eq::EqualityEngine* master);
  /** The master equality engine merged the classes of t1 and t2. */
  void notifyMasterMerge(TNode t1, TNode t2);

  // ---------------------------------------------------------- assertions
  size_t getNumAssertedFormulas() const { return d_assertedFormulas.size(); }

  TNode getAssertedFormula(size_t idx) const { return d_assertedFormulas[idx]; }

  /**
   * Internalize the asserted formula n, of the given generation: its subterms,
   * then its Boolean structure (assertRoot).
   */
  void internalizeAssertion(TNode n, uint32_t generation);

  // ----------------------------------------- propagation and backtracking
  /** Propagate both sides to a fixpoint; returns false on a conflict. */
  bool propagate();

  /** Whether either side has propagation work pending. */
  bool canPropagate() const;

  /**
   * Propagate on the theory side, after Boolean propagation and relevancy
   * have saturated: the assigned atoms, the equalities, the theories and the
   * quantifiers, in that order. Returns false on a conflict.
   */
  bool theoryPropagate();

  /** Whether the theory side has propagation work pending. */
  bool hasPendingTheoryWork() const;

  /** Called at the start of a search. */
  void initSearch();

  /**
   * The final check, when every relevant Boolean variable is assigned.
   * Returns true if it is done, and false if it made progress and the search
   * is to continue.
   */
  bool finalCheck();

  /**
   * Open a new scope: the Boolean side's, and the trail stack's, whose
   * context holds the scoped data of the relevancy propagator, the queue and
   * the fingerprints.
   */
  void pushScope();

  /**
   * Backtrack numScopes scopes: discard the pending work of the quantifier
   * manager, pop the Boolean side, then the trail stack (and its memory and
   * context) and the propagation queues, and reassert the units of the
   * scopes popped.
   */
  void popScope(size_t numScopes);

  /** Backtrack to the base level. */
  void popToBaseLvl();

  void resetCacheGeneration();

  // ----------------------------------------------------------- accessors

  Statistics& getStats() { return d_stats; }

  /** The E-graph. */
  EGraph& getEGraph() { return d_egraph; }

  const EGraph& getEGraph() const { return d_egraph; }

  // ------------------------------------- the Boolean search, see PropCore
  //
  // The methods below forward to the propositional side, d_prop. They are
  // the Boolean API that the theory side and the quantifier engine use.

  /** The propositional side. */
  PropCore& getPropCore() { return d_prop; }

  const PropCore& getPropCore() const { return d_prop; }

  BoolVar getBoolVar(TNode n) const { return d_prop.getBoolVar(n); }

  BoolVar getBoolVar(const ENode* n) const { return getBoolVar(n->getExpr()); }

  BoolVar getBoolVarOfId(size_t id) const { return d_prop.getBoolVarOfId(id); }

  Literal getLiteral(TNode n) const { return d_prop.getLiteral(n); }

  ENode* boolVar2ENode(BoolVar v) const
  {
    Assert(getBdata(v).isENode());
    return d_egraph.getENode(boolVar2Expr(v));
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

  BoolVarData& getBdata(BoolVar v) { return d_prop.getBdata(v); }

  const BoolVarData& getBdata(BoolVar v) const { return d_prop.getBdata(v); }

  bool hasENode(BoolVar v) const { return getBdata(v).isENode(); }

  SatValue getAssignment(Literal l) const { return d_prop.getAssignment(l); }

  SatValue getAssignment(BoolVar v) const { return d_prop.getAssignment(v); }

  SatValue getAssignment(TNode n) const { return d_prop.getAssignment(n); }

  SatValue getAssignment(ENode* n) const;

  uint32_t getScopeLevel() const { return d_prop.getScopeLevel(); }

  TNode boolVar2Expr(BoolVar v) const { return d_prop.boolVar2Expr(v); }

  bool isTrue(const ENode* n) const { return n == d_trueENode; }

  /** True if the input contains universal quantifiers. */
  bool hasQuantifiers() const { return d_hasQuantifiers; }

  // ----------------------------------------------- backtracking support
  template <typename TrailObject>
  void pushTrail(const TrailObject& obj)
  {
    d_trailStack.push(obj);
  }

  void pushTrailPtr(Trail* ptr) { d_trailStack.pushPtr(ptr); }

  TrailStack& getTrailStack() { return d_trailStack; }

  // ------------------------------------------------------ internalization
  bool bInternalized(TNode n) const { return d_prop.bInternalized(n); }

  bool litInternalized(TNode n) const { return d_prop.litInternalized(n); }

  /** The canonicalizer for quantifiers; see z3/ast.h. */
  QuantifierNormalizer& getNormalizer() { return d_normalizer; }

  /** The environment of the enclosing cvc5 solver. */
  const Env& getEnv() const { return d_env; }

  /**
   * Internalize the instance of the quantified formula q for terms, the
   * terms for its variables, in the form cvc5's theories take (see
   * mkInstance), and send it to cvc5. The instance is asserted at the
   * current scope.
   */
  void internalizeInstance(TNode q,
                           const std::vector<Node>& terms,
                           uint32_t generation);

  /**
   * Take the skolemization of the quantified formula q, which is assigned
   * false and relevant: assert the lemma of cvc5's quantifiers engine (see
   * mkSkolemization).
   */
  void skolemize(TNode q);

  void internalize(TNode n, bool gateCtx);
  void internalize(const Node* exprs, size_t numExprs, bool gateCtx);
  void internalize(TNode n, bool gateCtx, uint32_t generation);

  BoolVar mkBoolVar(TNode n) { return d_prop.mkBoolVar(n); }

  ENode* mkENode(TNode n, bool suppressArgs, bool mergeTf, bool cgcEnabled);

  /** Hand an assigned atom to the theory side; see propagateAtoms. */
  void enqueueAtom(Literal l) { d_atomPropagationQueue.push_back(l); }

  /** Called when the Boolean variable of n is deleted on backtracking. */
  void notifyBoolVarDeleted(TNode n);

  /**
   * Cache the generation of the enodes and quantifiers in n that backtracking
   * to newScopeLvl deletes, so that they are recreated with it.
   */
  void cacheGeneration(TNode n, uint32_t newScopeLvl);

  void mkGateClause(Literal l1, Literal l2) { d_prop.mkGateClause(l1, l2); }

  /**
   * Internalize n, a subterm of an assertion, in the given context; see
   * PropCore::assertRoot.
   */
  void internalizeRec(TNode n, bool gateCtx);

  // ------------------------------------------------------------ the input
  /** Assert a (prepared) formula. */
  void assertFormula(TNode e);
  /** Add e to the asserted formulas, splitting a top-level conjunction. */
  void pushAssertion(TNode e);
  /** Internalize the asserted formulas not internalized yet. */
  void internalizeAssertions();
  /**
   * Assert the root formula n: the clauses of a root gate over the literals
   * of its arguments, which are internalized here in turn, or the unit
   * literal of anything else.
   */
  void assertRoot(TNode n);
  void assertDefault(TNode n);

  void setEnodeFlag(BoolVar v, bool isNewVar);

  // ------------------------------------------------------------- engine
  void assign(Literal l) { d_prop.assign(l); }

  void setConflict() { d_prop.setConflict(); }

  bool inconsistent() const { return d_prop.inconsistent(); }

  bool isDiseq(ENode* n1, ENode* n2) const;

  /**
   * The classes of r1 and r2 are about to merge: relevancy spreads to the
   * class, and the quantifier manager is notified. Called by the E-graph.
   */
  void notifyMerge(ENode* r1, ENode* r2);
  /**
   * The Boolean classes of r1 and r2 merged, through n1 and n2: the value of
   * either is copied to the class. Called by the E-graph.
   */
  void propagateBoolENodeAssignment(ENode* r1, ENode* r2, ENode* n1, ENode* n2);

  // ------------------------------------------------------------ relevancy
  //
  // Relevancy belongs to the propositional side; see PropCore. The methods
  // below forward to it.

  /**
   * Notify the quantifier manager and the theories that n became relevant;
   * called by PropCore::notifyRelevant.
   */
  void notifyRelevant(TNode n);

  bool isRelevantCore(TNode n) const { return d_prop.isRelevantCore(n); }

  bool isRelevant(TNode n) const { return d_prop.isRelevant(n); }

  bool isRelevant(ENode* n) const { return isRelevant(n->getExpr()); }

  bool isRelevant(Literal l) const { return d_prop.isRelevant(l); }

  /** Whether E-matching considers n. */
  bool isRelevantForMatching(ENode* n) const { return isRelevant(n); }

  /** Whether the instance checkers consider n. */
  bool isRelevantForChecking(TNode n) const { return isRelevant(n); }

  bool isRelevantForChecking(ENode* n) const { return isRelevant(n); }

  void markAsRelevant(TNode n) { d_prop.markAsRelevant(n); }

  void markAsRelevant(ENode* n) { markAsRelevant(n->getExpr()); }

  void addRelevancyDependency(TNode source, TNode target)
  {
    d_prop.addRelevancyDependency(source, target);
  }

  /**
   * Rewrite a quantifier instance before it is internalized. Z3 applies its
   * th_rewriter here; this port uses cvc5's rewriter.
   */
  Node rewriteInstance(TNode n) const { return rewrite(n); }

  /**
   * True if the resource limits were exceeded during this search, which
   * then stays out of resources.
   */
  bool resourceLimitsExceeded();

  /** True if the resource limits were exceeded. */
  bool getCancelFlag();

 private:
  // -------------------------------------------- the boundary with cvc5
  /**
   * Prepare the search: internalize the asserted formulas and start the
   * search.
   */
  void setupSearch();
  /** Push or pop scopes until the scope level is lvl. */
  void setScopeLevel(uint32_t lvl);
  /**
   * The literal of n, an atom or a negated atom, internalizing the atom if
   * it is not internalized, for instance because it was deleted on
   * backtracking.
   */
  Literal literalOf(TNode n);
  /**
   * Cache the generations of the atoms of the units that will be reasserted
   * when backtracking to newScopeLvl.
   */
  void cacheUnitGenerations(uint32_t newScopeLvl);
  /** Reassert the units from unitsToReassertLim on, after a backtrack. */
  void reassertUnits(size_t unitsToReassertLim);
  /**
   * The decisions the core asks cvc5 for: each atom it splits on, whenever
   * it is unassigned. cvc5 asks its decision strategies before it decides
   * on its own.
   */
  class SplitStrategy : public theory::DecisionStrategy
  {
   public:
    SplitStrategy(Env& env, TheoryEngine*& te)
        : theory::DecisionStrategy(env), d_te(te)
    {
    }
    void initialize() override {}
    Node getNextDecisionRequest() override;
    std::string identify() const override { return "z3-split"; }
    /** Ask for a decision on the atom a. */
    void add(const Node& a) { d_atoms.push_back(a); }
    void clear() { d_atoms.clear(); }

   private:
    /** The engine of the core, for its prop engine. */
    TheoryEngine*& d_te;
    /** The atoms to decide. */
    std::vector<Node> d_atoms;
  };
  /** Pops the propositional side when the SAT context pops. */
  class PopNotify : public context::ContextNotifyObj
  {
   public:
    PopNotify(context::Context* c, SmtContext& hc)
        : context::ContextNotifyObj(c), d_hc(hc)
    {
    }

   protected:
    void contextNotifyPop() override { d_hc.notifyPop(); }

   private:
    SmtContext& d_hc;
  };
  /**
   * Send a lemma, which must not be preprocessed: its atoms are those of the
   * SAT solver.
   */
  void lemma(const Node& lem, theory::LemmaProperty p);
  /** Note a pop of the SAT context, which syncLevel follows. */
  void notifyPop();
  /** Push or pop the core's scopes to the level of the SAT context. */
  void syncLevel();
  /**
   * Note that the core is in conflict, which it leaves to cvc5's theories to
   * find; see enterConflict in smt_context.cpp.
   */
  void enterConflict();
  /**
   * Send the lemma lem, unless it was sent before, or send it again as a
   * lemma local to the SAT context if local is true.
   */
  void sendLemma(const Node& lem, bool local);
  /**
   * The lemma to send for lem. CaDiCaL restarts on a clause that is a unit
   * once the literals false at its base level are removed, to assign that
   * literal at the base level. Most conflicts and many instances are such
   * units here (the conflict that refutes a decision, the instance of an
   * asserted quantifier whose guards are asserted), and the restart undoes
   * every instance made since. Z3's search delays such units instead (its
   * delay_units). Below the second decision level, this
   * weakens such a lemma with the negation of the first decision, so that
   * CaDiCaL assigns its literal out of order at the first decision level
   * and backtracks at most one level (chronological backtracking). The
   * lemma itself is sent at the next check near the base level.
   */
  Node delayUnit(const Node& lem);
  /**
   * Make the relevant, unassigned variables of the core into decisions for
   * cvc5 (see SplitStrategy). These are the gates that relevancy needs
   * assigned, which cvc5 may leave unassigned when it stops on a partial
   * assignment.
   */
  void splitPendingAtoms();
  /**
   * Split on the variables that became relevant since the last call, which
   * cvc5 does not know and are still unassigned, as the core's relevancy
   * queue would decide them.
   */
  void splitNewlyRelevant();
  /** Have cvc5 decide v, unless it was asked before. */
  void split(BoolVar v);
  /** Propagate, and report what follows; returns false on a conflict. */
  bool propagateAndReport();
  /**
   * The core's form of n, a formula of cvc5: its quantified formulas over
   * the canonical variables the core expects (see z3/util/ast.h). The atoms
   * of n that change are recorded, for toHost.
   */
  Node toCore(TNode n);
  /** Record the atoms of n that its core's form nc renames, for toHost. */
  void recordRenamedAtoms(TNode n, TNode nc);
  /**
   * cvc5's form of n, a formula of the core: the atoms the core renamed are
   * cvc5's again. The other atoms, the new quantified formulas of the
   * instances for example, are the same for both.
   */
  Node toHost(TNode n);
  /**
   * The core's form of n, a formula of cvc5, in the form cvc5's theories
   * take, by cvc5's lemma preprocessing, adding to defs the definitions of
   * the skolems it introduces, and setting pp to the rewrite of n by the
   * preprocessing.
   */
  Node preprocessForTheories(TNode n,
                             std::vector<Node>& defs,
                             TrustNode& pp,
                             theory::InferenceId id);
  /**
   * The instance of the core's quantified formula q for terms, in the form
   * cvc5's theories take, see internalizeInstance. The lemma sent
   * for it is cvc5's instantiation lemma, proven by d_pg.
   */
  Node mkInstance(TNode q,
                  const std::vector<Node>& terms,
                  std::vector<Node>& defs);
  /**
   * The skolemization of the core's quantified formula q, in the form cvc5's
   * theories take, see skolemize. The lemma sent for it is
   * the one of cvc5's quantifiers engine, with its proof.
   */
  Node mkSkolemization(TNode q, std::vector<Node>& defs);
  /**
   * The lemma of cvc5's Skolemize utility that skolemizes q, which the
   * quantifiers engine sent when q was asserted false.
   */
  TrustNode getSkolemization(TNode q);
  /**
   * Preprocess the lemma trn proves, which the core sends, into the form
   * cvc5's theories take, as mkInstance and mkSkolemization do.
   */
  Node preprocessLemma(const TrustNode& trn,
                       std::vector<Node>& defs,
                       theory::InferenceId id);

  /** The engine, for the prop engine's state. */
  TheoryEngine* d_te;
  /** Where lemmas go. */
  theory::quantifiers::QuantifiersInferenceManager& d_qim;
  /** Whether the propositional side was set up (presolve). */
  bool d_setup;
  /** Whether the core is in conflict in the current context. */
  bool d_inConflict;
  /** The level of the SAT context at which the conflict was found. */
  uint32_t d_conflictLevel;
  /** Whether cvc5 must call check again. */
  bool d_needCheck;
  /**
   * The lowest level the SAT context popped to since the last syncLevel, or
   * UINT32_MAX if it did not pop.
   */
  uint32_t d_popLevel;
  /** The atoms registered by cvc5 before the next check. */
  std::vector<Node> d_preregistered;
  /** The lemmas sent, which are permanent in cvc5. */
  std::unordered_set<Node> d_lemmasSent;
  /** The lemmas weakened by delayUnit, to send as they are, see check. */
  std::vector<Node> d_delayedUnits;
  /**
   * For each atom of cvc5 that toCore renamed, the core's form and cvc5's.
   * Alpha-equivalent atoms of cvc5 would have the same core's form, which
   * does not happen with the inputs the core takes: the core's forms keep
   * the quantifier names (qid) and patterns.
   */
  std::unordered_map<Node, Node> d_hostAtom;
  /** The atoms split on, see split. */
  std::unordered_set<Node> d_splitAtoms;
  /**
   * Proves the lemmas the core sends, and gives, for an instance or the
   * definition of a skolem, the lemma cvc5 is sent for it.
   */
  std::unique_ptr<LemmaProofGenerator> d_pg;
  /**
   * The inference of each lemma the core sends, in cvc5's form: an instance,
   * a skolemization, or the definition of a skolem in one of these, which
   * has the inference of that lemma. A weakened lemma has the inference of
   * the lemma it weakens.
   */
  std::unordered_map<Node, theory::InferenceId> d_lemmaIds;
  /** See SplitStrategy. */
  std::unique_ptr<SplitStrategy> d_splitStrategy;
  /** Follows the pops of the SAT context. */
  std::unique_ptr<PopNotify> d_popNotify;
  /** Gives the core the literals the SAT solver asserts. */
  std::unique_ptr<RelevancyTracker> d_tracker;

 protected:
  // --------------------------------------------- equality and congruence
  void propagateBoolENodeAssignmentCore(ENode* source, ENode* target);
  bool addDiseq(ENode* n1, ENode* n2);
  bool isDiseqCore(ENode* n1, ENode* n2, bool checkDistinctRootValues) const;

  void assignQuantifier(TNode q);
  /**
   * Internalize the formula norm, in the form cvc5's theories take, with the
   * definitions defs of the skolems in it, after sending them to cvc5: norm as
   * an instance if instance is true, and otherwise as a lemma that holds
   * globally.
   */
  void internalizePreprocessed(TNode norm,
                               const std::vector<Node>& defs,
                               uint32_t generation,
                               bool instance);

  // ----------------------------------------------------------- the search
  bool propagateAtoms();
  void propagateBoolVarENode(BoolVar v);

  // --------------------------------------------------------- backtracking

  // -------------------------------------------------------- internalization
  void updateGeneration(ENode* n);
  void updateGeneration(TNode e)
  {
    if (isApp(e) && d_egraph.eInternalized(e))
    {
      updateGeneration(d_egraph.getENode(e));
    }
  }
  void internalizeFormula(TNode n, bool gateCtx);
  void internalizeEq(TNode n, bool gateCtx);
  void internalizeDistinct(TNode n, bool gateCtx);
  void internalizeQuantifier(TNode q, bool gateCtx);
  void internalizeFormulaCore(TNode n, bool gateCtx);
  void setMergeTf(ENode* n, BoolVar v, bool isNewVar);
  void internalizeTerm(TNode n);
  void internalizeUninterpreted(TNode n);

  void init();
  void flush();

  // ------------------------------------------------------------- the fields
  /**
   * The trail of the theory side, and the memory of the enodes, relevancy
   * handlers, fingerprints, code trees and quantifier statistics. Its context
   * holds the scoped data of the relevancy propagator, the queue and the
   * fingerprints, so it is declared before them.
   */
  TrailStack d_trailStack;
  /**
   * The propositional side: the Boolean search state. It refers to d_stats
   * and d_trailStack, so it is declared after them.
   */
  PropCore d_prop;
  /** The E-graph. */
  EGraph d_egraph;
  QuantifierNormalizer d_normalizer;
  /**
   * The forms of the instances made so far, by (SEXPR q t1 ... tn). The core
   * makes an instance again after backtracking, and mkInstance gives
   * the same form then, without the skolem definitions it gave the first time.
   */
  std::unordered_map<Node, Node> d_instanceForms;
  /** The quantifiers: E-matching and instantiation. */
  QuantifierManager d_qmanager;

  /** The enodes of the constants true and false. */
  ENode* d_trueENode;
  ENode* d_falseENode;

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

  // ------------------------------------------------------ input and scopes
  /** The formulas asserted to the core, and how far they are internalized. */
  std::vector<Node> d_assertedFormulas;
  size_t d_assertedFormulasQhead;
  bool d_hasQuantifiers;
  bool d_internalizingAssertions;
  /** Whether the search started (setupSearch). */
  bool d_searching;
  /** Whether the resource limits were exceeded during this search. */
  bool d_resourceOut;
  /** A unit literal that is reasserted after every backtrack. */
  struct ReplayUnit
  {
    Node d_unit;
    bool d_sign;
    bool d_relevant;
  };
  std::vector<ReplayUnit> d_unitsToReassert;
  /** For each scope, the size of d_unitsToReassert when it was pushed. */
  std::vector<size_t> d_unitsToReassertLims;

  // ------------------------------------------------------------ backtracking

  /** A temporary variable used during internalization. */
  uint32_t d_generation;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIERS__SMT_CONTEXT_H */
