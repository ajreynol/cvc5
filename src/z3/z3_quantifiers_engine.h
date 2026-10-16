/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The quantifiers engine of the ported Z3 core.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__Z3_QUANTIFIERS_ENGINE_H
#define CVC5__Z3__Z3_QUANTIFIERS_ENGINE_H

#include <memory>

#include "theory/quantifiers_engine.h"
#include "z3/assertion_preparation.h"
#include "z3/host_core.h"
#include "z3/shared_backend.h"

namespace cvc5::internal {

namespace theory {
class OutputChannel;
}

namespace z3 {

/**
 * The quantifiers engine of cvc5's quantifiers theory with --z3, which owns
 * the ported core. cvc5's own theories do the ground reasoning, with their
 * equality engines and theory combination; the core matches and instantiates
 * over a shadow of the ground state:
 * - it receives a copy of every literal the SAT solver asserts, for its
 *   E-graph and for relevancy (the quantifiers theory observes every fact),
 *   and the equalities cvc5's theories derive, through the master equality
 *   engine, which notifies this engine (ShadowFeed);
 * - it sends lemmas only (instances, conflicts and splits), which need no
 *   explanation, and reports no propagations;
 * - the formulas it asserts go through cvc5's preprocessing first.
 *
 * None of the modules of cvc5's quantifiers engine are made. What it keeps of
 * the native engine is skolemization: a quantified formula asserted false is
 * skolemized with the lemma of cvc5's Skolemize utility, which the core
 * asserts as it does an instance.
 */
class Z3QuantifiersEngine : public theory::QuantifiersEngine,
                            public HostCoreOutput
{
 public:
  Z3QuantifiersEngine(Env& env,
                      theory::OutputChannel& out,
                      theory::quantifiers::QuantifiersState& qs,
                      theory::quantifiers::QuantifiersRegistry& qr,
                      theory::quantifiers::TermRegistry& tr,
                      theory::quantifiers::QuantifiersInferenceManager& qim,
                      ProofNodeManager* pnm);
  ~Z3QuantifiersEngine();
  /**
   * Make a fresh core, for the theory engine te, after its prop engine was
   * made.
   */
  void resetCore(TheoryEngine* te);
  /**
   * Prepare the preprocessed assertions for the core (AssertionPreparation),
   * and assert them to it. The prepared formulas are those cvc5 converts.
   */
  void prepareAssertions(const std::vector<Node>& assertions,
                         std::vector<Node>& prepared);

  //--------------------------------------------- the quantifiers engine
  /** None: the model builder of TheoryEngine is the default one. */
  theory::quantifiers::QModelBuilder* getModelBuilder() const override
  {
    return nullptr;
  }
  void presolve() override;
  void ppNotifyAssertions(
      CVC5_UNUSED const std::vector<Node>& assertions) override
  {
  }
  /** Run the core, at standard and full effort. */
  void check(theory::Theory::Effort e) override;
  void notifyCombineTheories() override {}
  void preRegisterQuantifier(Node q) override;
  /** Give the fact to the core, and skolemize, see above. */
  void assertFact(TNode atom, bool pol, TNode fact) override;
  void eqNotifyNewClass(CVC5_UNUSED TNode t) override {}
  /** Give the merge to the feed of the shadow. */
  void eqNotifyMerge(TNode t1, TNode t2) override;

  //------------------------------------- HostCoreOutput, through the channel
  void lemma(const Node& lem, theory::LemmaProperty p) override;
  void setModelUnsound(theory::IncompleteId id) override;

 private:
  /** Nothing to initialize, as no module is made. */
  void finishInit(TheoryEngine* te) override;

  /** The output channel of the quantifiers theory. */
  theory::OutputChannel& d_out;
  /** The ported core. */
  SharedBackend d_backend;
  /** The core under cvc5's prop engine. */
  std::unique_ptr<HostCore> d_core;
  /** The preparation of assertions for the core. */
  AssertionPreparation d_prep;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__Z3_QUANTIFIERS_ENGINE_H */
