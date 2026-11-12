/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The logical context: the eager E-matching core.
 *
 * Ported from Z3: src/smt/smt_context.h.
 * Z3 is Copyright (c) Microsoft Corporation and licensed under the MIT
 * License, see licenses/z3-LICENSE.
 *
 * The coordinator of the core: it owns and drives the Boolean side (PropCore),
 * the E-graph (EGraph) and the quantifiers (QuantifierManager), internalizes
 * the input and the instances into the first two, and runs the propagation
 * fixpoint and the scopes. EagerEMatching, the boundary with cvc5, drives it.
 * The ground reasoning is cvc5's theories', whose equalities reach the E-graph
 * through the master equality engine (EGraph::notifyMasterMerge).
 *
 * Of Z3's context, only what E-matching and quantifier instantiation need
 * is ported: not its search (decisions, conflict resolution, restarts, lemma
 * garbage collection), its theory plugins, proof production, or Z3's
 * asserted_formulas preprocessing pipeline (cvc5's Preprocessor is used
 * instead).
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__SMT_CONTEXT_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__SMT_CONTEXT_H

#include <memory>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/eager/bool_var_data.h"
#include "theory/quantifiers/eager/clause.h"
#include "theory/quantifiers/eager/egraph.h"
#include "theory/quantifiers/eager/enode.h"
#include "theory/quantifiers/eager/prop_core.h"
#include "theory/quantifiers/eager/quantifier_manager.h"
#include "theory/quantifiers/eager/quantifier_normalizer.h"
#include "theory/quantifiers/eager/relevancy.h"
#include "theory/quantifiers/eager/statistics.h"
#include "theory/quantifiers/eager/trail.h"
#include "theory/quantifiers/eager/watch_list.h"

namespace cvc5::internal {

namespace theory::quantifiers::eager {

class QuantifierManager;
class EagerEMatching;

/**
 * The ported core: the coordinator of the Boolean side (PropCore), the E-graph
 * (EGraph) and the quantifiers (QuantifierManager).
 *
 * EagerEMatching drives it: it asserts the input and the facts of cvc5, sets
 * its scope level to follow the SAT context, and runs the propagation and the
 * final check. The core sends its instances back through EagerEMatching
 * (mkInstance, sendLemma), and takes the skolemizations of cvc5's quantifiers
 * engine from it (mkSkolemization) without sending them.
 */
class SmtContext final : protected EnvObj
{
 public:
  /**
   * The core of the module host, which sends its instances and lemmas to
   * cvc5.
   */
  SmtContext(Env& env, EagerEMatching& host);
  ~SmtContext();

  SmtContext(const SmtContext&) = delete;
  SmtContext& operator=(const SmtContext&) = delete;

  // -------------------------------------- the search, driven by EagerEMatching
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
    return d_encodedDistincts.contains(n);
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

  /** Clear the generations cacheGeneration saved, after a backtrack. */
  void resetCacheGeneration();

  // ----------------------------------------------------------- accessors

  /** The statistics of the core. */
  Statistics& getStats() { return d_stats; }

  /** The E-graph. */
  EGraph& getEGraph() { return d_egraph; }

  /** The E-graph, read-only. */
  const EGraph& getEGraph() const { return d_egraph; }

  // ------------------------------- the Boolean side, and the bridge to the
  //                                 E-graph
  /** The propositional side. */
  PropCore& getPropCore() { return d_prop; }

  /** The propositional side, read-only. */
  const PropCore& getPropCore() const { return d_prop; }

  /** The enode of the Boolean variable v, which must have one. */
  ENode* boolVar2ENode(SatVariable v) const
  {
    Assert(d_prop.getBdata(v).isENode());
    return d_egraph.getENode(d_prop.boolVar2Expr(v));
  }

  /** The Boolean variable of the Boolean enode n, other than false's. */
  SatVariable enode2BoolVar(const ENode* n) const
  {
    Assert(n->isBool());
    Assert(n != d_falseENode);
    return d_prop.getBoolVarOfId(n->getOwnerId());
  }

  /** The literal of the Boolean enode n: the false literal for false's. */
  SatLiteral enode2Literal(const ENode* n) const
  {
    Assert(n->isBool());
    return n == d_falseENode ? s_falseLiteral : SatLiteral(enode2BoolVar(n));
  }

  /** The value of the Boolean variable of the Boolean enode n. */
  SatValue getAssignment(ENode* n) const;

  /** The current scope level of the core. */
  uint32_t getScopeLevel() const { return d_trailStack.getScopeLevel(); }

  /** Whether n is the enode of true. */
  bool isTrue(const ENode* n) const { return n == d_trueENode; }

  // ----------------------------------------------- backtracking support
  /** The trail stack, which undoes the theory side's changes on a pop. */
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
   * Internalize the skolemization of the quantified formula q, which is
   * assigned false and relevant: the lemma that cvc5's quantifiers engine
   * sent when cvc5 asserted q false (see mkSkolemization). This is only so
   * that its witnesses are relevant to the core, through q, as the core's
   * own formulas make them; the lemma is cvc5's, and the core does not send
   * it. If cvc5 has not skolemized q yet, which is when the core assigned q
   * false before cvc5's SAT solver did, q waits for retrySkolemizations.
   */
  void skolemize(TNode q);
  /**
   * Skolemize the quantified formulas whose skolemization cvc5 had not sent
   * when the core skolemized them, if they are still assigned false and
   * relevant. Called after cvc5's facts are given to the core, since cvc5
   * skolemizes q when it asserts q false.
   */
  void retrySkolemizations();

  /**
   * Internalize n, in a gate context if gateCtx, with the given generation,
   * or the current one if none is given.
   */
  void internalize(TNode n, bool gateCtx);
  void internalize(TNode n, bool gateCtx, uint32_t generation);

  /**
   * Make the enode of n, with its generation, at the current scope level; the
   * flags are those of EGraph::mkENode. An equality that already holds is
   * assigned true.
   */
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
  /**
   * Assert n as a unit: internalize it in a gate context, then assign its
   * literal true and relevant, or set a conflict if it is false.
   */
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

  /** Mark v as having an enode, on the trail unless v is new (isNewVar). */
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
   * True if the resource limits were exceeded during this search, which
   * then stays out of resources.
   */
  bool resourceLimitsExceeded();

  /** True if the resource limits were exceeded. */
  bool getCancelFlag();

 protected:
  // --------------------------------------------- equality and congruence
  /**
   * Copy the assignment of the variable of source, which is assigned, to the
   * variables of the members of its class, from target on.
   */
  void propagateBoolENodeAssignmentCore(ENode* source, ENode* target);

  /** q is assigned true: the quantifier manager matches its patterns. */
  void assignQuantifier(TNode q);
  /**
   * Internalize the formula norm, in the form cvc5's theories take, with the
   * definitions defs of the skolems in it, after sending the definitions to
   * cvc5, and norm too if it is an instance (instance is true).
   */
  void internalizePreprocessed(TNode norm,
                               const std::vector<Node>& defs,
                               uint32_t generation,
                               bool instance);

  // ----------------------------------------------------------- the search
  /**
   * Propagate the assigned atoms of d_atomPropagationQueue: their enodes,
   * their equalities to the E-graph, and their quantifiers, matched if true
   * and skolemized if false. Returns false on a conflict.
   */
  bool propagateAtoms();
  /**
   * Cache the generations of the atoms of the units that will be reasserted
   * when backtracking to newScopeLvl.
   */
  void cacheUnitGenerations(uint32_t newScopeLvl);
  /** Reassert the units from unitsToReassertLim on, after a backtrack. */
  void reassertUnits(size_t unitsToReassertLim);
  /**
   * Propagate the value of v to its enode: merge it with true or false if
   * its merge_tf flag is set, and assign the value to the other members of
   * its class.
   */
  void propagateBoolVarENode(SatVariable v);

  // --------------------------------------------------------- backtracking

  // -------------------------------------------------------- internalization
  /**
   * Lower the generation of the enode n (or of the enode of e, if any) to
   * the current generation, if that is positive and lower. Equalities are
   * skipped, as patterns have none.
   */
  void updateGeneration(ENode* n);
  void updateGeneration(TNode e)
  {
    if (isApp(e) && d_egraph.eInternalized(e))
    {
      updateGeneration(d_egraph.getENode(e));
    }
  }
  /**
   * Internalize the formula n: its Boolean variable, and an enode when it is
   * not in a gate context. Equalities, distincts and quantifiers go to their
   * own cases, and the other formulas to internalizeFormulaCore.
   */
  void internalizeFormula(TNode n, bool gateCtx);
  /** Internalize the equality n of non-Boolean terms, flagged as one. */
  void internalizeEq(TNode n, bool gateCtx);
  /** Internalize the distinct n as equivalent to its pairwise expansion. */
  void internalizeDistinct(TNode n, bool gateCtx);
  /**
   * Internalize the quantifier q as a Boolean variable, with an enode if it
   * is not in a gate context, and add a forall to the quantifier manager.
   */
  void internalizeQuantifier(TNode q, bool gateCtx);
  /**
   * Internalize the gate or predicate n: its arguments, its Boolean
   * variable, its enode if it needs one, then its gate constraints.
   */
  void internalizeFormulaCore(TNode n, bool gateCtx);
  /**
   * Set the merge_tf flag of n, the enode of v, on the trail unless v is new
   * (isNewVar), and merge n with true or false if v is assigned.
   */
  void setMergeTf(ENode* n, SatVariable v, bool isNewVar);
  /** Internalize the term n, or update its generation if it has an enode. */
  void internalizeTerm(TNode n);
  /**
   * Make the enode of the application n, after its arguments', with
   * congruence closure enabled unless n is an arithmetic sum or product.
   */
  void internalizeUninterpreted(TNode n);

  /** Make the enodes of true and false. */
  void init();
  /** Flush relevancy, and reset the trail stack and the Boolean side. */
  void flush();

  // ------------------------------------------------------------- the fields
  /** The search statistics. */
  Statistics d_stats;
  /** The module that owns the core, its boundary with cvc5. */
  EagerEMatching& d_host;
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
  /** Rewrites quantifiers over the canonical variables. */
  QuantifierNormalizer d_normalizer;
  /**
   * The forms of the instances made so far, by (SEXPR q t1 ... tn): true for
   * an instance that rewrites to true, null for one not yet made. The core
   * makes an instance again after backtracking, and mkInstance gives the
   * same form then, without the skolem definitions it gave the first time.
   * They are in the user context, as cvc5's preprocessing, which gives the
   * skolem definitions again after a user pop.
   */
  context::CDHashMap<Node, Node> d_instanceForms;
  /** The quantifiers: E-matching and instantiation. */
  QuantifierManager d_qmanager;

  /** The enodes of the constants true and false. */
  ENode* d_trueENode;
  ENode* d_falseENode;

  /** The assigned atoms waiting for propagateAtoms. */
  std::vector<SatLiteral> d_atomPropagationQueue;

  /**
   * The generations cacheGeneration saved, of the terms and quantifiers a
   * backtrack deletes, for when they are recreated.
   */
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
  /** The nodes cacheGeneration visited since resetCacheGeneration. */
  std::unordered_set<TNode> d_cacheGenerationVisited;

  // ------------------------------------------------------ input and scopes
  /**
   * The formulas asserted to the core, and how far they are internalized,
   * in the scope of the user level they were asserted at.
   */
  context::CDList<Node> d_assertedFormulas;
  context::CDO<size_t> d_assertedFormulasQhead;
  /** The root distincts that assertDistinct encoded. */
  context::CDHashSet<Node> d_encodedDistincts;
  /**
   * The equalities f(a_i) = v_i made by assertDistinct, which are kept alive
   * here.
   */
  std::vector<Node> d_distinctEqs;
  /** Whether internalizeAssertions is running, which it does not reenter. */
  bool d_internalizingAssertions;
  /** Whether the search started (setupSearch). */
  bool d_searching;
  /**
   * The scope level of the current search's assertions, Z3's base level:
   * the user scopes of cvc5, where this core's scope level 0 is cvc5's SAT
   * context level 1.
   */
  uint32_t d_baseLevel;
  /** Whether the resource limits were exceeded during this search. */
  bool d_resourceOut;
  /** A unit literal that is reasserted after every backtrack. */
  struct ReplayUnit
  {
    /** The atom of the unit. */
    Node d_unit;
    /** Whether the unit is the negation of the atom. */
    bool d_sign;
    /** Whether the unit is marked relevant. */
    bool d_relevant;
  };
  std::vector<ReplayUnit> d_unitsToReassert;
  /** The quantified formulas waiting for retrySkolemizations. */
  std::unordered_set<Node> d_pendingSkolemizations;
  /** For each scope, the size of d_unitsToReassert when it was pushed. */
  context::CDList<size_t> d_unitsToReassertLims;

  /**
   * The generation given to the terms internalized now (0 outside of an
   * instance), see generationOf.
   */
  uint32_t d_generation;
};

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER__SMT_CONTEXT_H */
