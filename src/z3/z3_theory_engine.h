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
  /** Follow a pop of the SAT context. */
  void notifyPop();
  /** Send the conflict made of the host literals lits. */
  void sendConflict(const std::vector<Literal>& lits);
  /** Send the formulas recorded by the propositional side as lemmas. */
  void sendLemmas();
  /**
   * Collect the literals the propositional side assigned since the last
   * call, other than those the host asserted, that are atoms of cvc5's
   * search, as propagations.
   */
  void collectPropagations();
  /**
   * Make the relevant, unassigned theory atoms that cvc5 does not know, which
   * the theory side expects the search to decide (for instance the case
   * splits of datatypes, or the equalities of model-based combination), into
   * decisions for cvc5, with a splitting lemma.
   */
  void splitPendingAtoms();
  /** Propagate, and report what follows; returns false on a conflict. */
  bool propagateAndReport();
  /** The node of the literal l. */
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
  /** Follows the pops of the SAT context. */
  std::unique_ptr<PopNotify> d_popNotify;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__Z3_THEORY_ENGINE_H */
