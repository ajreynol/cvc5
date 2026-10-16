/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The ported core in the quantifiers slot of cvc5's theory engine.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__THEORY_SLOT_H
#define CVC5__Z3__THEORY_SLOT_H

#include <memory>
#include <string>

#include "theory/theory.h"
#include "theory/theory_state.h"
#include "z3/host_core.h"
#include "z3/shared_backend.h"

namespace cvc5::internal {

class TheoryEngine;

namespace z3 {

/**
 * The quantifiers slot of cvc5's theory engine, held by the ported core
 * (--z3). cvc5's own theories do the ground reasoning, with their equality
 * engines and theory combination; the core matches and instantiates over a
 * shadow of the ground state:
 * - it receives a copy of every literal the SAT solver asserts, for its
 *   E-graph and for relevancy, and the equalities cvc5's theories derive,
 *   through the master equality engine (ShadowFeed);
 * - it sends lemmas only (instances, conflicts and splits), which need no
 *   explanation, and reports no propagations;
 * - the formulas it asserts go through cvc5's lemma preprocessing first.
 *
 * Preprocessing (the rewriter, ppRewrite, solving equalities) is done by an
 * instance of cvc5's quantifiers theory, whose quantifiers engine is not
 * used.
 */
class TheorySlot : public theory::Theory, public HostCoreOutput
{
 public:
  TheorySlot(Env& env,
             theory::OutputChannel& out,
             theory::Valuation valuation,
             TheoryEngine& te);
  ~TheorySlot();
  /** The ported core. */
  SharedBackend& getBackend() { return d_backend; }
  /** The core under cvc5's prop engine. */
  HostCore& getCore() { return *d_core; }

  //------------------------------------------- preprocessing, by cvc5's theory
  theory::TheoryRewriter* getTheoryRewriter() override;
  ProofRuleChecker* getProofChecker() override;
  void finishInit() override;
  /**
   * The master equality engine, as cvc5's quantifiers theory takes, which
   * notifies the feed of the shadow.
   */
  bool needsEqualityEngine(theory::EeSetupInfo& esi) override;
  bool ppAssert(TrustNode tin,
                theory::TrustSubstitutionMap& outSubstitutions) override;
  TrustNode ppRewrite(TNode n, std::vector<theory::SkolemLemma>& lems) override;
  TrustNode ppStaticRewrite(TNode n) override;

  //------------------------------------------------ the search, by the core
  void preRegisterTerm(TNode n) override;
  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;
  void postCheck(Effort level) override;
  void presolve() override;
  std::string identify() const override;

  //------------------------------------- HostCoreOutput, through the channel
  void lemma(const Node& lem, theory::LemmaProperty p) override;
  void setModelUnsound(theory::IncompleteId id) override;

 private:
  /** The ported core. */
  SharedBackend d_backend;
  /** The core under cvc5's prop engine. */
  std::unique_ptr<HostCore> d_core;
  /** cvc5's quantifiers theory, for preprocessing. */
  std::unique_ptr<theory::Theory> d_native;
  /** The state, which check requires. */
  theory::TheoryState d_state;
};

/** Put a TheorySlot in the quantifiers slot of te (--z3). */
void addTheorySlots(Env& env, TheoryEngine& te);

/** The slot of te, which must have been filled by addTheorySlots. */
TheorySlot& getTheorySlot(TheoryEngine& te);

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__THEORY_SLOT_H */
