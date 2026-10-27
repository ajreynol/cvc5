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
 * The theory side of the core: the E-graph (congruence closure over
 * enodes), the internalizer, and the quantifier manager. Its propositional
 * side, PropCore, mirrors cvc5's assignment (see syncLevel); the ground
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
#include "z3/quantifiers/cg_table.h"
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
 * The ported core: the theory side, whose propositional side is PropCore, and
 * the boundary with cvc5.
 *
 * It implements the search contract of cvc5's prop engine (preregistration,
 * facts and checks) over PropCore, which mirrors the assignment for the theory
 * side (see PropCore::hostInit). Its scopes follow the SAT context.
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
  //
  // The asserted formulas and the checks are driven by the propositional
  // side, PropCore. The methods below forward to it for the theory side.

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
  void initSearch();

  /**
   * The final check, when every relevant Boolean variable is assigned.
   * Returns true if it is done, and false if it made progress and the search
   * is to continue.
   */
  bool finalCheck();

  /** Push a scope of the theory side, after the propositional side's. */
  void pushTheoryScope();

  /**
   * Discard the pending work of the quantifier manager, before the Boolean
   * variables are unassigned.
   */
  void popTheoryScopeBegin();

  /**
   * Pop numScopes scopes of the theory side, after the Boolean variables are
   * unassigned: the trail stack, which pops the trail (and its memory) and
   * the data in its context, and the propagation queues.
   */
  void popTheoryScopeEnd(size_t numScopes);

  void resetCacheGeneration();

  // ----------------------------------------------------------- accessors

  Statistics& getStats() { return d_stats; }

  ENode* getENode(TNode n) const
  {
    Assert(eInternalized(n));
    return d_app2ENode[n.getId()];
  }

  /** Like getENode, but returns null if n is not internalized. */
  ENode* findENode(TNode n) const
  {
    size_t id = n.getId();
    return id < d_app2ENode.size() ? d_app2ENode[id] : nullptr;
  }

  TNode getNextInEClass(TNode n) const
  {
    ENode* e = findENode(n);
    return e == nullptr ? TNode::null() : TNode(e->getNext()->getExpr());
  }

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

  /** True if the input contains universal quantifiers. */
  bool hasQuantifiers() const { return d_prop.hasQuantifiers(); }

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

  bool eInternalized(TNode n) const { return findENode(n) != nullptr; }

  size_t getNumEInternalized() const { return d_eInternalizedStack.size(); }

  TNode getEInternalized(size_t idx) const { return d_eInternalizedStack[idx]; }

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

  // ---------------------------------------------------- trail callbacks
  /** Undo an addEq; invoked from the trail. */
  void undoAddEq(ENode* r1, size_t r2NumParents);

  /** Undo a congruence class generation merge; invoked from the trail. */
  void undoMergeCgcGenerations(ENode* e1,
                               uint32_t e1Generation,
                               ENode* e2,
                               uint32_t e2Generation);

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

  void setEnodeFlag(BoolVar v, bool isNewVar);

  // ------------------------------------------------------------- engine
  void assign(Literal l) { d_prop.assign(l); }

  void addEq(ENode* n1, ENode* n2);

  void setConflict() { d_prop.setConflict(); }

  bool inconsistent() const { return d_prop.inconsistent(); }

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

  /** An enode congruent to decl(args), or null if there is none. */
  ENode* getENodeEqTo(TNode decl,
                      bool commutative,
                      size_t numArgs,
                      ENode* const* args);

  bool canPropagate() const { return d_prop.canPropagate(); }

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
   * A dense id for a declaration, created on demand. This is the counterpart
   * of Z3's func_decl::get_small_id, which the E-matching engine uses to index
   * its tables by function symbol.
   */
  uint32_t getDeclId(TNode decl);
  /** The dense id of decl, or UINT32_MAX if it has none yet. */
  uint32_t getDeclIdOption(TNode decl) const;

  bool resourceLimitsExceeded() { return d_prop.resourceLimitsExceeded(); }

  bool getCancelFlag() { return d_prop.getCancelFlag(); }

 private:
  // -------------------------------------------- the boundary with cvc5
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
   * Queue in the E-graph the merges of the master equality engine notified
   * since the last call, and those of the terms the core internalized since
   * then, for its next propagation.
   */
  void applyMasterMerges();
  /** The term of the core recorded for the representative rep, or null. */
  Node masterTermOf(TNode rep) const;
  /** Merge a and b, which the master equality engine made equal, if both
   * are internalized. */
  void mergeMasterTerms(TNode a, TNode b);
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
  /**
   * The master equality engine, which collects the terms and merges of the
   * equality engines of cvc5's theories, or null. Its merges are the
   * E-graph's, besides the congruences they imply: they are queued as they
   * are notified (notifyMasterMerge), and applied at the next check
   * (applyMasterMerges). The master equality engine keeps no reasons, so the
   * core cannot explain these merges, and it does not need to: the core
   * keeps no explanations.
   */
  theory::eq::EqualityEngine* d_masterEe;
  /**
   * For a representative of the master equality engine, a term of the core
   * in its class, in the SAT context.
   */
  context::CDHashMap<Node, Node> d_masterTerm;
  /**
   * How many of the terms the core internalized were looked up in the
   * master equality engine. In the SAT context, as the core's scopes are.
   */
  context::CDO<size_t> d_masterIdx;
  /**
   * The merges notified since the last check, as the representative that
   * survived and the one that was merged into it. The SAT context popping
   * voids them.
   */
  std::vector<std::pair<Node, Node>> d_pendingMerges;
  /** Gives the core the literals the SAT solver asserts. */
  std::unique_ptr<RelevancyTracker> d_tracker;

 protected:
  // --------------------------------------------- equality and congruence
  struct NewEq
  {
    ENode* d_lhs;
    ENode* d_rhs;
    NewEq(ENode* lhs, ENode* rhs) : d_lhs(lhs), d_rhs(rhs) {}
  };

  void removeParentsFromCgTable(ENode* r1);
  void reinsertParentsIntoCgTable(ENode* r1, ENode* r2);
  void mergeCgcGenerations(ENode* e1, uint32_t e1Generation, ENode* e2);
  void setGenerationSticky(ENode* e, uint32_t generation);
  void propagateBoolENodeAssignment(ENode* r1, ENode* r2, ENode* n1, ENode* n2);
  void propagateBoolENodeAssignmentCore(ENode* source, ENode* target);
  void applyStickyUpdates(ENode* e1,
                          uint32_t e1Generation,
                          ENode* e2,
                          uint32_t e2Generation);

  void pushEq(ENode* lhs, ENode* rhs)
  {
    if (lhs->getRoot() != rhs->getRoot())
    {
      d_eqPropagationQueue.push_back(NewEq(lhs, rhs));
    }
  }

  void pushNewCongruence(ENode* n1, ENode* n2)
  {
    Assert(n1->d_cg == n2);
    pushEq(n1, n2);
  }

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
  bool propagateEqs();
  bool propagateAtoms();
  void propagateBoolVarENode(BoolVar v);

  // --------------------------------------------------------- backtracking

  // -------------------------------------------------------- internalization
  void updateGeneration(ENode* n);
  void updateGeneration(TNode e)
  {
    if (isApp(e) && eInternalized(e))
    {
      updateGeneration(getENode(e));
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
  void undoMkENode();

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
  QuantifierNormalizer d_normalizer;
  /**
   * The forms of the instances made so far, by (SEXPR q t1 ... tn). The core
   * makes an instance again after backtracking, and mkInstance gives
   * the same form then, without the skolem definitions it gave the first time.
   */
  std::unordered_map<Node, Node> d_instanceForms;
  /** The quantifiers: E-matching and instantiation. */
  QuantifierManager d_qmanager;

  /** The expressions already internalized as enodes. */
  std::vector<Node> d_eInternalizedStack;

  // ------------------------------------- equality and uninterpreted functions
  ENode* d_trueENode;
  ENode* d_falseENode;
  /** Maps the id of a term to its enode. */
  App2ENode d_app2ENode;
  ENodeVector d_enodes;
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

  // ------------------------------------------------------------ backtracking

  /** A temporary variable used during internalization. */
  uint32_t d_generation;

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

#endif /* CVC5__Z3__QUANTIFIERS__SMT_CONTEXT_H */
