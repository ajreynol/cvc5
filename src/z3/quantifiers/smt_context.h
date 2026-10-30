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
 * the input and the instances into the first two, and runs the propagation
 * fixpoint and the scopes. Z3Module, the boundary with cvc5, drives it. The
 * ground reasoning is cvc5's theories', whose equalities reach the E-graph
 * through the master equality engine (EGraph::notifyMasterMerge).
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

#include "context/cdlist.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "z3/quantifiers/egraph.h"
#include "z3/quantifiers/enode.h"
#include "z3/quantifiers/quantifier_manager.h"
#include "z3/quantifiers/quantifier_normalizer.h"
#include "z3/quantifiers/statistics.h"
#include "z3/quantifiers/trail.h"
#include "z3/relevancy/bool_var_data.h"
#include "z3/relevancy/clause.h"
#include "z3/relevancy/prop_core.h"
#include "z3/relevancy/relevancy.h"
#include "z3/relevancy/watch_list.h"

namespace cvc5::internal {

namespace z3 {

class QuantifierManager;
class Z3Module;

/**
 * The ported core: the coordinator of the Boolean side (PropCore), the E-graph
 * (EGraph) and the quantifiers (QuantifierManager).
 *
 * Z3Module drives it: it asserts the input and the facts of cvc5, sets its
 * scope level to follow the SAT context, and runs the propagation and the
 * final check. The core sends its instances and skolemizations back through
 * Z3Module (mkInstance, mkSkolemization, sendLemma).
 */
class SmtContext final : protected EnvObj
{
 public:
  /**
   * The core of the module host, which sends its instances and lemmas to
   * cvc5.
   */
  SmtContext(Env& env, Z3Module& host);
  ~SmtContext();

  SmtContext(const SmtContext&) = delete;
  SmtContext& operator=(const SmtContext&) = delete;

  // -------------------------------------- the search, driven by Z3Module
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
  SatLiteral literalOf(TNode n);
  /**
   * Whether n is a root distinct encoded by assertDistinct, which, as in Z3,
   * has no Boolean variable: the host's assignment of it is ignored.
   */
  bool isEncodedDistinct(TNode n) const
  {
    return d_encodedDistincts.find(n) != d_encodedDistincts.end();
  }
  /** Assert a (prepared) formula. */
  void assertFormula(TNode e);

  // ---------------------------------------------------------- assertions
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

  // ------------------------------- the Boolean side, and the bridge to the
  //                                 E-graph
  /** The propositional side. */
  PropCore& getPropCore() { return d_prop; }

  const PropCore& getPropCore() const { return d_prop; }

  ENode* boolVar2ENode(SatVariable v) const
  {
    Assert(d_prop.getBdata(v).isENode());
    return d_egraph.getENode(d_prop.boolVar2Expr(v));
  }

  SatVariable enode2BoolVar(const ENode* n) const
  {
    Assert(n->isBool());
    Assert(n != d_falseENode);
    return d_prop.getBoolVarOfId(n->getOwnerId());
  }

  SatLiteral enode2Literal(const ENode* n) const
  {
    Assert(n->isBool());
    return n == d_falseENode ? s_falseLiteral : SatLiteral(enode2BoolVar(n));
  }

  SatValue getAssignment(ENode* n) const;

  uint32_t getScopeLevel() const { return d_trailStack.getScopeLevel(); }

  bool isTrue(const ENode* n) const { return n == d_trueENode; }

  // ----------------------------------------------- backtracking support
  TrailStack& getTrailStack() { return d_trailStack; }

  // ------------------------------------------------------ internalization
  /** The canonicalizer for quantifiers; see quantifier_normalizer.h. */
  QuantifierNormalizer& getNormalizer() { return d_normalizer; }

  /**
   * Internalize the instance of the quantified formula q for terms, the
   * terms for its variables, in the form cvc5's theories take (see
   * mkInstance), and send it to cvc5. The instance is asserted at the
   * current scope. Returns false, and makes nothing, if the instance
   * rewrites to true.
   */
  bool internalizeInstance(TNode q,
                           const std::vector<Node>& terms,
                           uint32_t generation);

  /**
   * Take the skolemization of the quantified formula q, which is assigned
   * false and relevant: assert the lemma of cvc5's quantifiers engine (see
   * mkSkolemization).
   */
  void skolemize(TNode q);

  void internalize(TNode n, bool gateCtx);
  void internalize(TNode n, bool gateCtx, uint32_t generation);

  ENode* mkENode(TNode n, bool suppressArgs, bool mergeTf, bool cgcEnabled);

  /** Hand an assigned atom to the theory side; see propagateAtoms. */
  void enqueueAtom(SatLiteral l) { d_atomPropagationQueue.push_back(l); }

  /** Called when the Boolean variable of n is deleted on backtracking. */
  void notifyBoolVarDeleted(TNode n);

  /**
   * Cache the generation of the enodes and quantifiers in n that backtracking
   * to newScopeLvl deletes, so that they are recreated with it.
   */
  void cacheGeneration(TNode n, uint32_t newScopeLvl);

  /**
   * Internalize n, a subterm of an assertion, in the given context; see
   * PropCore::assertRoot.
   */
  void internalizeRec(TNode n, bool gateCtx);

  // ------------------------------------------------------------ the input
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
  /**
   * Assert the root distinct n. As in Z3 (assert_distinct), a distinct with
   * more than 32 arguments is not expanded into its pairwise disequalities:
   * each argument a_i is instead asserted to be mapped by a fresh function f
   * to a fresh interpreted value v_i, so that merging two arguments merges
   * two values, which is a conflict. Every Verus query asserts such a
   * distinct over its fuel constants (150 to 700 of them), whose expansion
   * made up most of the core's Boolean variables and enodes.
   */
  void assertDistinct(TNode n);

  void setEnodeFlag(SatVariable v, bool isNewVar);

  // ------------------------------------------------------------- engine
  /**
   * True if n1 and n2 are known to be distinct: their roots are distinct
   * constants, or their equality is relevant and false.
   */
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
  /**
   * Notify the quantifier manager and the theories that n became relevant;
   * called by PropCore::notifyRelevant.
   */
  void notifyRelevant(TNode n);

  /**
   * Rewrite a quantifier instance before it is internalized. Z3 applies its
   * th_rewriter here; this port uses cvc5's rewriter.
   */
  /**
   * True if the resource limits were exceeded during this search, which
   * then stays out of resources.
   */
  bool resourceLimitsExceeded();

  /** True if the resource limits were exceeded. */
  bool getCancelFlag();

 protected:
  // --------------------------------------------- equality and congruence
  void propagateBoolENodeAssignmentCore(ENode* source, ENode* target);

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
  /**
   * Cache the generations of the atoms of the units that will be reasserted
   * when backtracking to newScopeLvl.
   */
  void cacheUnitGenerations(uint32_t newScopeLvl);
  /** Reassert the units from unitsToReassertLim on, after a backtrack. */
  void reassertUnits(size_t unitsToReassertLim);
  void propagateBoolVarENode(SatVariable v);

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
  void setMergeTf(ENode* n, SatVariable v, bool isNewVar);
  void internalizeTerm(TNode n);
  void internalizeUninterpreted(TNode n);

  void init();
  void flush();

  // ------------------------------------------------------------- the fields
  /** The search statistics. */
  Statistics d_stats;
  /** The module that owns the core, its boundary with cvc5. */
  Z3Module& d_host;
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
   * The forms of the instances made so far, by (SEXPR q t1 ... tn): true for
   * an instance that rewrites to true, null for one not yet made. The core
   * makes an instance again after backtracking, and mkInstance gives the
   * same form then, without the skolem definitions it gave the first time.
   */
  std::unordered_map<Node, Node> d_instanceForms;
  /** The quantifiers: E-matching and instantiation. */
  QuantifierManager d_qmanager;

  /** The enodes of the constants true and false. */
  ENode* d_trueENode;
  ENode* d_falseENode;

  std::vector<SatLiteral> d_atomPropagationQueue;

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
  /** The root distincts that assertDistinct encoded. */
  std::unordered_set<Node> d_encodedDistincts;
  /**
   * The equalities f(a_i) = v_i made by assertDistinct, which are kept alive
   * here.
   */
  std::vector<Node> d_distinctEqs;
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
  context::CDList<size_t> d_unitsToReassertLims;

  /**
   * The generation given to the terms internalized now (0 outside of an
   * instance), see generationOf.
   */
  uint32_t d_generation;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIERS__SMT_CONTEXT_H */
