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
 */

#include "z3/theory_slot.h"

#include "smt/env.h"
#include "theory/ee_setup_info.h"
#include "theory/output_channel.h"
#include "theory/quantifiers/theory_quantifiers.h"
#include "theory/theory_engine.h"
#include "z3/shadow_feed.h"

namespace cvc5::internal {
namespace z3 {

TheorySlot::TheorySlot(Env& env,
                       theory::OutputChannel& out,
                       theory::Valuation valuation,
                       TheoryEngine& te)
    : Theory(theory::THEORY_QUANTIFIERS, env, out, valuation, "z3slot::"),
      d_backend(env),
      d_core(std::make_unique<HostCore>(env, d_backend, te, *this)),
      d_native(new theory::quantifiers::TheoryQuantifiers(env, out, valuation)),
      d_state(env, valuation)
{
  d_theoryState = &d_state;
  // TheoryEngine checks the slot even when no fact was asserted, as the core
  // may have work left from the previous check (see HostCore::check).
  d_checkEarlyExit = false;
  // The core takes a copy of every fact.
  d_observeAllFacts = true;
}

TheorySlot::~TheorySlot() {}

theory::TheoryRewriter* TheorySlot::getTheoryRewriter()
{
  return d_native->getTheoryRewriter();
}

ProofRuleChecker* TheorySlot::getProofChecker()
{
  return d_native->getProofChecker();
}

bool TheorySlot::needsEqualityEngine(theory::EeSetupInfo& esi)
{
  esi.d_useMaster = true;
  esi.d_notify = d_core->getShadowFeed();
  return true;
}

void TheorySlot::finishInit()
{
  d_core->getShadowFeed()->setMasterEqualityEngine(d_equalityEngine);
  static_cast<theory::quantifiers::TheoryQuantifiers*>(d_native.get())
      ->finishInit();
}

bool TheorySlot::ppAssert(TrustNode tin,
                          theory::TrustSubstitutionMap& outSubstitutions)
{
  return d_native->ppAssert(tin, outSubstitutions);
}

TrustNode TheorySlot::ppRewrite(TNode n, std::vector<theory::SkolemLemma>& lems)
{
  return d_native->ppRewrite(n, lems);
}

TrustNode TheorySlot::ppStaticRewrite(TNode n)
{
  return d_native->ppStaticRewrite(n);
}

void TheorySlot::preRegisterTerm(TNode n)
{
  // The core takes the atoms of the SAT solver; it internalizes the terms
  // under them itself.
  if (n.getType().isBoolean() && d_valuation.isSatLiteral(n))
  {
    d_core->preRegister(n);
  }
}

bool TheorySlot::preNotifyFact(TNode /*atom*/,
                               bool /*pol*/,
                               TNode fact,
                               bool /*isPrereg*/,
                               bool /*isInternal*/)
{
  d_core->assertFact(fact);
  return true;
}

void TheorySlot::postCheck(Effort level) { d_core->check(level); }

void TheorySlot::presolve() { d_core->presolve(); }

std::string TheorySlot::identify() const { return "z3::TheorySlot"; }

void TheorySlot::lemma(const Node& lem, theory::LemmaProperty p)
{
  d_out->lemma(lem,
               theory::InferenceId::UNKNOWN,
               p | theory::LemmaProperty::UNPROCESSED);
}

void TheorySlot::setModelUnsound(theory::IncompleteId id)
{
  d_out->setModelUnsound(id);
}

void addTheorySlots(Env& env, TheoryEngine& te)
{
  te.addTheory(
      theory::THEORY_QUANTIFIERS,
      [&env, &te](theory::OutputChannel& out, theory::Valuation valuation) {
        return new TheorySlot(env, out, valuation, te);
      });
}

TheorySlot& getTheorySlot(TheoryEngine& te)
{
  TheorySlot* s =
      dynamic_cast<TheorySlot*>(te.theoryOf(theory::THEORY_QUANTIFIERS));
  Assert(s != nullptr);
  return *s;
}

}  // namespace z3
}  // namespace cvc5::internal
