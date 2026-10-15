/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory engine of the ported Z3 core.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__Z3_THEORY_ENGINE_H
#define CVC5__Z3__Z3_THEORY_ENGINE_H

#include <memory>
#include <unordered_set>
#include <utility>
#include <vector>

#include "context/context.h"
#include "theory/theory_engine.h"
#include "z3/shared_backend.h"
#include "z3/util/literal.h"

namespace cvc5::internal {
namespace z3 {

/**
 * The theory engine used with --z3, paired by smt::EngineFactory with
 * Z3PropEngine, or, with --z3-prop-engine=cvc5, with Z3HostedPropEngine.
 *
 * The theory reasoning of the search happens in the theory side of the
 * ported core, SmtContext, which this class owns, with the propositional
 * side, through its SharedBackend; see that class for how their lifetime
 * follows this engine's.
 *
 * The inherited TheoryEngine, with cvc5's theories, is kept as a service to
 * cvc5's preprocessing, which uses it for theory rewriting and
 * preprocessing, static learning, solving equalities and sort inference, and
 * through which the theory rewriters are registered. It also holds what
 * preprocessing reports through setRefutationUnsound and setModelUnsound,
 * which Z3PropEngine applies to the result of the search. The theories never
 * receive an assertion, so anything else asked of them is not about the
 * problem. The commands that would ask are refused through
 * Z3PropEngine::supports, and the options through
 * SetDefaults::checkZ3Capabilities.
 *
 * Hosted (--z3-prop-engine=cvc5), this class also implements the search
 * contract that cvc5's prop engine uses (preRegister, assertFact, check,
 * propagations, explanations), over the propositional side of the core in
 * host mode, which mirrors the assignment for the theory side (see
 * PropCore::hostInit). Its scopes follow the SAT context.
 */
class Z3TheoryEngine : public TheoryEngine
{
 public:
  Z3TheoryEngine(Env& env, bool hosted = false);
  ~Z3TheoryEngine() override;
  /** Get the state shared with the paired Z3PropEngine. */
  SharedBackend& getBackend() { return d_backend; }
  /** Whether cvc5's prop engine drives this engine. */
  bool isHosted() const { return d_hosted; }
  /** Forget the state of the previous context; see Z3HostedPropEngine. */
  void hostReset();

  // ------------------------------------------- the search contract, hosted
  void preRegister(TNode atom) override;
  void assertFact(TNode literal) override;
  void check(theory::Theory::Effort effort) override;
  bool presolve() override;
  void postsolve(prop::SatValue result) override;
  void notifyRestart() override;
  void getPropagatedLiterals(std::vector<TNode>& literals) override;
  Node getNextDecisionRequest() override;
  TrustNode getExplanation(TNode literal) override;
  bool needCheck() const override;

 private:
  /** Pops the propositional side when the SAT context pops. */
  class PopNotify : public context::ContextNotifyObj
  {
   public:
    PopNotify(context::Context* c, Z3TheoryEngine& te)
        : context::ContextNotifyObj(c), d_te(te)
    {
    }

   protected:
    void contextNotifyPop() override { d_te.notifyPop(); }

   private:
    Z3TheoryEngine& d_te;
  };
  /** Note a pop of the SAT context, which syncLevel follows. */
  void notifyPop();
  /** Push or pop the core's scopes to the level of the SAT context. */
  void syncLevel();
  /** Send the conflict made of the host literals lits. */
  void sendConflict(const std::vector<Literal>& lits);
  /** Send the formulas recorded by the propositional side as lemmas. */
  void sendLemmas();
  /**
   * Send the lemma lem, unless it was sent before, or send it again as a
   * lemma local to the SAT context if local is true.
   */
  void sendLemma(const Node& lem, bool local, bool notifyDecisions);
  /**
   * The lemma to send for lem. CaDiCaL restarts on a clause that is a unit
   * once the literals false at its base level are removed, to assign that
   * literal at the base level. Most conflicts and many instances are such
   * units here (the conflict that refutes a decision, the instance of an
   * asserted quantifier whose guards are asserted), and the restart undoes
   * every instance made since. Z3's search delays such units instead (see
   * PropCore::resolveConflict). Below the second decision level, this
   * weakens such a lemma with the negation of the first decision, so that
   * CaDiCaL assigns its literal out of order at the first decision level
   * and backtracks at most one level (chronological backtracking). The
   * lemma itself is sent at the next check near the base level, with
   * notifyDecisions as given.
   */
  Node delayUnit(const Node& lem, bool notifyDecisions);
  /**
   * Collect the literals the propositional side assigned since the last
   * call, other than those the host asserted, that are atoms of cvc5's
   * search, as propagations.
   */
  void collectPropagations();
  /**
   * Make the relevant, unassigned variables of the core into decisions for
   * cvc5, with a splitting lemma (or v (not v)) that cvc5's decision heuristic
   * must justify, unless one was sent before. These are the atoms the theory
   * side expects the search to decide (for instance the case splits of
   * datatypes, or the equalities of model-based combination), and the gates
   * that relevancy needs assigned, which cvc5 may leave unassigned when it
   * stops on a partial assignment.
   */
  void splitPendingAtoms();
  /**
   * Split on the variables that became relevant since the last call, which
   * cvc5 does not know and are still unassigned, as the core's relevancy
   * queue would decide them.
   */
  void splitNewlyRelevant();
  /** Send the splitting lemma for v, unless it was sent before. */
  void split(BoolVar v);
  /** Propagate, and report what follows; returns false on a conflict. */
  bool propagateAndReport();
  /** The node of the literal l, as cvc5 knows it. */
  Node literalNode(Literal l);

  /** The ported core. */
  SharedBackend d_backend;
  /** Whether cvc5's prop engine drives this engine. */
  bool d_hosted;
  /** Whether the propositional side was set up (presolve). */
  bool d_setup;
  /** Whether a conflict was sent in the current context. */
  bool d_conflictSent;
  /** Whether cvc5 must call check again, see needCheck. */
  bool d_needCheck;
  /** The propagations not yet given to cvc5. */
  std::vector<Node> d_propagations;
  /** How far in the assigned literals propagations were collected. */
  size_t d_reportIdx;
  /** The atoms registered by cvc5 before the next check. */
  std::vector<Node> d_preregistered;
  /** The lemmas sent, which are permanent in cvc5. */
  std::unordered_set<Node> d_lemmasSent;
  /**
   * The lemmas weakened by delayUnit, to send as they are, see check, with
   * whether cvc5's decision heuristic must justify them.
   */
  std::vector<std::pair<Node, bool>> d_delayedUnits;
  /** Follows the pops of the SAT context. */
  std::unique_ptr<PopNotify> d_popNotify;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__Z3_THEORY_ENGINE_H */
