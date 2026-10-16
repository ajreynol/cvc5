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
 */

#include "z3/z3_quantifiers_engine.h"

#include "theory/output_channel.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/skolemize.h"
#include "z3/shadow_feed.h"

namespace cvc5::internal {
namespace z3 {

Z3QuantifiersEngine::Z3QuantifiersEngine(
    Env& env,
    theory::OutputChannel& out,
    theory::quantifiers::QuantifiersState& qs,
    theory::quantifiers::QuantifiersRegistry& qr,
    theory::quantifiers::TermRegistry& tr,
    theory::quantifiers::QuantifiersInferenceManager& qim,
    ProofNodeManager* pnm)
    : QuantifiersEngine(env, qs, qr, tr, qim, pnm),
      d_out(out),
      d_backend(env),
      d_core(std::make_unique<HostCore>(env, d_backend, *this))
{
}

Z3QuantifiersEngine::~Z3QuantifiersEngine() {}

void Z3QuantifiersEngine::finishInit(TheoryEngine* /*te*/) {}

void Z3QuantifiersEngine::presolve()
{
  // the master equality engine, which notifies this engine of its merges
  d_core->getShadowFeed()->setMasterEqualityEngine(
      d_qstate.getEqualityEngine());
  d_core->presolve();
}

void Z3QuantifiersEngine::check(theory::Theory::Effort e)
{
  if (e != theory::Theory::EFFORT_LAST_CALL)
  {
    d_core->check(e);
  }
}

void Z3QuantifiersEngine::preRegisterQuantifier(Node q)
{
  // The core takes the atoms of the SAT solver; it internalizes the terms
  // under them itself.
  if (d_qstate.getValuation().isSatLiteral(q))
  {
    d_core->preRegister(q);
  }
}

void Z3QuantifiersEngine::assertFact(TNode atom, bool pol, TNode fact)
{
  d_core->assertFact(fact);
  if (pol || atom.getKind() != Kind::FORALL)
  {
    return;
  }
  // A quantified formula asserted false is skolemized, as cvc5's quantifiers
  // engine does. Z3's preparation of the input leaves only universal
  // quantifiers, in positive positions, but cvc5 may still decide one false.
  // The lemma is made once per user context, and goes through the core
  // rather than straight to cvc5 (see SmtContext::skolemize), which asserts
  // it again each time the formula is asserted false after a backtrack.
  theory::quantifiers::Skolemize* sk = d_qim.getSkolemize();
  sk->process(atom);
  Node lem = sk->getSkolemizationLemma(atom);
  Assert(!lem.isNull());
  d_core->skolemize(atom, lem);
}

void Z3QuantifiersEngine::eqNotifyMerge(TNode t1, TNode t2)
{
  d_core->getShadowFeed()->eqNotifyMerge(t1, t2);
}

void Z3QuantifiersEngine::lemma(const Node& lem, theory::LemmaProperty p)
{
  d_out.lemma(lem,
              theory::InferenceId::UNKNOWN,
              p | theory::LemmaProperty::UNPROCESSED);
}

void Z3QuantifiersEngine::setModelUnsound(theory::IncompleteId id)
{
  d_out.setModelUnsound(id);
}

}  // namespace z3
}  // namespace cvc5::internal
