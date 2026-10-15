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
 */

#include "z3/theory_slot.h"

#include <sstream>

#include "smt/env.h"
#include "theory/output_channel.h"
#include "theory/theory_engine.h"
#include "theory/theory_traits.h"

namespace cvc5::internal {
namespace z3 {

namespace {

/** cvc5's own theory for the slot id. */
theory::Theory* mkNativeTheory(Env& env,
                               theory::OutputChannel& out,
                               theory::Valuation valuation,
                               theory::TheoryId id)
{
  switch (id)
  {
    case theory::THEORY_BUILTIN:
      return new theory::builtin::TheoryBuiltin(env, out, valuation);
    case theory::THEORY_BOOL:
      return new theory::booleans::TheoryBool(env, out, valuation);
    case theory::THEORY_UF:
      return new theory::uf::TheoryUF(env, out, valuation);
    case theory::THEORY_ARITH:
      return new theory::arith::TheoryArith(env, out, valuation);
    case theory::THEORY_BV:
      return new theory::bv::TheoryBV(env, out, valuation);
    case theory::THEORY_FF:
      return new theory::ff::TheoryFiniteFields(env, out, valuation);
    case theory::THEORY_FP:
      return new theory::fp::TheoryFp(env, out, valuation);
    case theory::THEORY_ARRAYS:
      return new theory::arrays::TheoryArrays(env, out, valuation);
    case theory::THEORY_DATATYPES:
      return new theory::datatypes::TheoryDatatypes(env, out, valuation);
    case theory::THEORY_SEP:
      return new theory::sep::TheorySep(env, out, valuation);
    case theory::THEORY_SETS:
      return new theory::sets::TheorySets(env, out, valuation);
    case theory::THEORY_BAGS:
      return new theory::bags::TheoryBags(env, out, valuation);
    case theory::THEORY_STRINGS:
      return new theory::strings::TheoryStrings(env, out, valuation);
    case theory::THEORY_QUANTIFIERS:
      return new theory::quantifiers::TheoryQuantifiers(env, out, valuation);
    default: Unhandled() << "no theory for " << id;
  }
  return nullptr;
}

}  // namespace

// ------------------------------------------------------------ SlotBackend

SlotBackend::SlotBackend(Env& env, TheoryEngine& te)
    : d_backend(env),
      d_slots(theory::THEORY_LAST, nullptr),
      d_driver(theory::THEORY_LAST)
{
  d_core = std::make_unique<HostCore>(env, d_backend, te, *this);
  // The driver is the slot TheoryEngine checks last: the enabled one with
  // the largest id, BOOL and BUILTIN having no check.
  const LogicInfo& logic = env.getLogicInfo();
  for (theory::TheoryId id = theory::THEORY_FIRST; id < theory::THEORY_LAST;
       ++id)
  {
    if (id != theory::THEORY_BUILTIN && id != theory::THEORY_BOOL
        && logic.isTheoryEnabled(id))
    {
      d_driver = id;
    }
  }
}

SlotBackend::~SlotBackend() {}

void SlotBackend::registerSlot(TheorySlot* s) { d_slots[s->getId()] = s; }

void SlotBackend::drainOtherSlots()
{
  for (TheorySlot* s : d_slots)
  {
    if (s != nullptr && s->getId() != d_driver)
    {
      s->drainFacts();
    }
  }
}

theory::OutputChannel& SlotBackend::out()
{
  Assert(d_driver != theory::THEORY_LAST && d_slots[d_driver] != nullptr);
  return d_slots[d_driver]->out();
}

void SlotBackend::lemma(const Node& lem,
                        theory::LemmaProperty p,
                        bool /*notifyDecisions*/)
{
  // The decision heuristic justifies every lemma here, which is the default
  // of --z3-host-axiom-decisions.
  out().lemma(lem,
              theory::InferenceId::UNKNOWN,
              p | theory::LemmaProperty::UNPROCESSED);
}

void SlotBackend::propagate(const Node& lit) { out().propagate(lit); }

void SlotBackend::preferPhase(TNode atom, bool phase)
{
  out().preferPhase(atom, phase);
}

void SlotBackend::setModelUnsound(theory::IncompleteId id)
{
  out().setModelUnsound(id);
}

// ------------------------------------------------------------- TheorySlot

TheorySlot::TheorySlot(Env& env,
                       theory::OutputChannel& out,
                       theory::Valuation valuation,
                       theory::TheoryId id,
                       std::shared_ptr<SlotBackend> sb)
    : Theory(id, env, out, valuation, "z3slot::"),
      d_sb(sb),
      d_native(mkNativeTheory(env, out, valuation, id)),
      d_state(env, valuation),
      d_draining(false)
{
  d_theoryState = &d_state;
  // The driver's check runs the core even when its own fact queue is empty:
  // the facts may be queued at the other slots. TheoryEngine then also
  // checks the slots when no fact was asserted at all, as the hosted engine
  // runs the core at every check: the core may have work left from the
  // previous one (see HostCore::needCheck).
  d_checkEarlyExit = false;
  d_sb->registerSlot(this);
}

TheorySlot::~TheorySlot() {}

void TheorySlot::drainFacts()
{
  // check, with d_draining set, gives the facts to the core (preNotifyFact)
  d_draining = true;
  check(EFFORT_STANDARD);
  d_draining = false;
}

theory::TheoryRewriter* TheorySlot::getTheoryRewriter()
{
  return d_native->getTheoryRewriter();
}

ProofRuleChecker* TheorySlot::getProofChecker()
{
  return d_native->getProofChecker();
}

void TheorySlot::finishInit()
{
  // cvc5's theory gets an equality engine of its own, as it would under its
  // own theory engine, unless it asks for the master one, which only the
  // quantifiers engine provides.
  if (getId() == theory::THEORY_QUANTIFIERS)
  {
    static_cast<theory::quantifiers::TheoryQuantifiers*>(d_native.get())
        ->finishInit();
  }
  else
  {
    d_native->finishInitStandalone();
  }
}

void TheorySlot::ppStaticLearn(TNode in, std::vector<TrustNode>& learned)
{
  d_native->ppStaticLearn(in, learned);
}

bool TheorySlot::ppAssert(TrustNode tin,
                          theory::TrustSubstitutionMap& outSubstitutions)
{
  return d_native->ppAssert(tin, outSubstitutions);
}

TrustNode TheorySlot::ppRewrite(TNode n,
                                std::vector<theory::SkolemLemma>& lems)
{
  return d_native->ppRewrite(n, lems);
}

TrustNode TheorySlot::ppStaticRewrite(TNode n)
{
  return d_native->ppStaticRewrite(n);
}

void TheorySlot::ppNotifyAssertions(const std::vector<Node>& assertions)
{
  // the quantifiers engine of cvc5's quantifiers theory is not used
  if (getId() != theory::THEORY_QUANTIFIERS)
  {
    d_native->ppNotifyAssertions(assertions);
  }
}

void TheorySlot::preRegisterTerm(TNode n)
{
  // The core takes the atoms of the SAT solver; it internalizes the terms
  // under them itself.
  if (n.getType().isBoolean() && d_valuation.isSatLiteral(n))
  {
    d_sb->getCore().preRegister(n);
  }
}

bool TheorySlot::preCheck(Effort /*level*/)
{
  if (d_draining)
  {
    // the driver takes the facts of this slot
    return false;
  }
  if (!d_sb->isDriver(getId()))
  {
    // left to the driver
    return true;
  }
  d_sb->drainOtherSlots();
  return false;
}

bool TheorySlot::preNotifyFact(TNode /*atom*/,
                               bool /*pol*/,
                               TNode fact,
                               bool /*isPrereg*/,
                               bool /*isInternal*/)
{
  d_sb->getCore().assertFact(fact);
  return true;
}

void TheorySlot::postCheck(Effort level)
{
  if (!d_draining && d_sb->isDriver(getId()))
  {
    d_sb->getCore().check(level);
  }
}

TrustNode TheorySlot::explain(TNode n)
{
  return TrustNode::mkTrustPropExp(n, d_sb->getCore().explain(n), nullptr);
}

void TheorySlot::presolve() { d_sb->getCore().presolve(); }

std::string TheorySlot::identify() const
{
  std::stringstream ss;
  ss << "z3::TheorySlot(" << getId() << ")";
  return ss.str();
}

// ------------------------------------------------------------ construction

void addTheorySlots(Env& env, TheoryEngine& te)
{
  std::shared_ptr<SlotBackend> sb = std::make_shared<SlotBackend>(env, te);
  for (theory::TheoryId id = theory::THEORY_FIRST; id < theory::THEORY_LAST;
       ++id)
  {
    te.addTheory(id,
                 [&env, id, sb](theory::OutputChannel& out,
                                theory::Valuation valuation) {
                   return new TheorySlot(env, out, valuation, id, sb);
                 });
  }
}

SlotBackend& getSlotBackend(TheoryEngine& te)
{
  TheorySlot* s = dynamic_cast<TheorySlot*>(te.theoryOf(theory::THEORY_BUILTIN));
  Assert(s != nullptr);
  return s->getSlotBackend();
}

}  // namespace z3
}  // namespace cvc5::internal
