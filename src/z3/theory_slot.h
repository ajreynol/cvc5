/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The ported core in the theory slots of cvc5's theory engine.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__THEORY_SLOT_H
#define CVC5__Z3__THEORY_SLOT_H

#include <memory>
#include <string>
#include <vector>

#include "theory/theory.h"
#include "theory/theory_state.h"
#include "z3/host_core.h"
#include "z3/shared_backend.h"

namespace cvc5::internal {

class TheoryEngine;

namespace z3 {

class TheorySlot;

/**
 * What the theory slots share: the ported core (SharedBackend), driven by a
 * HostCore whose output goes through the output channel of the driver slot.
 * The driver is the enabled slot with the largest id other than BOOL and
 * BUILTIN, which TheoryEngine checks last (QUANTIFIERS in a quantified
 * logic): its check gives the core the facts queued at every slot, then
 * does what the hosted engine's check does. See ARCHITECTURE_PLAN.md,
 * section 16. With --z3-slots=quantifiers, QUANTIFIERS is the only slot,
 * and it receives a copy of every fact (section 17).
 */
class SlotBackend : public HostCoreOutput
{
 public:
  SlotBackend(Env& env, TheoryEngine& te);
  ~SlotBackend();
  SharedBackend& getBackend() { return d_backend; }
  HostCore& getCore() { return *d_core; }
  /** Register the slot s, made for its theory id. */
  void registerSlot(TheorySlot* s);
  /** Whether the slot of id is the driver. */
  bool isDriver(theory::TheoryId id) const { return id == d_driver; }
  /** Give the core the facts queued at every slot but the driver. */
  void drainOtherSlots();

  // ------------------------------------- HostCoreOutput, through the driver
  void lemma(const Node& lem,
             theory::LemmaProperty p,
             bool notifyDecisions) override;
  void propagate(const Node& lit) override;
  void preferPhase(TNode atom, bool phase) override;
  void setModelUnsound(theory::IncompleteId id) override;

 private:
  /** The output channel of the driver slot. */
  theory::OutputChannel& out();

  /** The ported core. */
  SharedBackend d_backend;
  /** The logic, for the enabled slots. */
  const LogicInfo& d_logic;
  /** The core under cvc5's prop engine. */
  std::unique_ptr<HostCore> d_core;
  /** The slots, by theory id. */
  std::vector<TheorySlot*> d_slots;
  /** The id of the driver slot. */
  theory::TheoryId d_driver;
};

/**
 * A theory slot of cvc5's theory engine, held by the ported core, under
 * --z3-theory-engine=cvc5. It requests no equality engine. Preprocessing
 * (the rewriter, ppRewrite, static learning, solving equalities) is done by
 * an instance of cvc5's own theory for the slot, with an equality engine of
 * its own, as when cvc5's theories serve the port's preprocessing under its
 * own theory engine. The search is done by the shared core: every slot hands
 * it the atoms it registers and the facts it is asserted, and the driver
 * slot runs it.
 */
class TheorySlot : public theory::Theory
{
 public:
  TheorySlot(Env& env,
             theory::OutputChannel& out,
             theory::Valuation valuation,
             theory::TheoryId id,
             std::shared_ptr<SlotBackend> sb);
  ~TheorySlot();
  /** The backend the slots share. */
  SlotBackend& getSlotBackend() { return *d_sb; }
  /** Give the core the facts queued at this slot. */
  void drainFacts();
  /** The output channel of this slot. */
  theory::OutputChannel& out() { return *d_out; }

  //------------------------------------------- preprocessing, by cvc5's theory
  theory::TheoryRewriter* getTheoryRewriter() override;
  ProofRuleChecker* getProofChecker() override;
  void finishInit() override;
  /**
   * None, except for the quantifiers slot when the core is a shadow fed by
   * the equalities of cvc5's theories: it takes the master equality engine,
   * as cvc5's quantifiers theory does, which notifies the feed.
   */
  bool needsEqualityEngine(theory::EeSetupInfo& esi) override;
  void ppStaticLearn(TNode in, std::vector<TrustNode>& learned) override;
  bool ppAssert(TrustNode tin,
                theory::TrustSubstitutionMap& outSubstitutions) override;
  TrustNode ppRewrite(TNode n, std::vector<theory::SkolemLemma>& lems) override;
  TrustNode ppStaticRewrite(TNode n) override;
  void ppNotifyAssertions(const std::vector<Node>& assertions) override;

  //------------------------------------------------ the search, by the core
  void preRegisterTerm(TNode n) override;
  bool preCheck(Effort level) override;
  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;
  void postCheck(Effort level) override;
  TrustNode explain(TNode n) override;
  void presolve() override;
  std::string identify() const override;

 private:
  /** The backend the slots share. */
  std::shared_ptr<SlotBackend> d_sb;
  /** cvc5's own theory for the slot, for preprocessing. */
  std::unique_ptr<theory::Theory> d_native;
  /** The state, which check requires. */
  theory::TheoryState d_state;
  /** Whether the driver is taking the facts of this slot, see drainFacts. */
  bool d_draining;
};

/**
 * Fill every theory slot of te with a TheorySlot, all sharing one
 * SlotBackend (--z3-theory-engine=cvc5).
 */
void addTheorySlots(Env& env, TheoryEngine& te);

/** The backend the slots of te share; te must have been filled by
 * addTheorySlots. */
SlotBackend& getSlotBackend(TheoryEngine& te);

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__THEORY_SLOT_H */
