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
#include "z3/smt_context.h"

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
      d_core(std::make_unique<HostCore>(env, d_backend, *this)),
      d_prep(env)
{
}

void Z3QuantifiersEngine::resetCore(TheoryEngine* te)
{
  d_backend.resetContext();
  d_core->reset(te);
}

void Z3QuantifiersEngine::prepareAssertions(const std::vector<Node>& assertions,
                                            std::vector<Node>& prepared)
{
  d_prep.apply(
      d_backend.getContext(), d_backend.getPropCore(), assertions, prepared);
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

void Z3QuantifiersEngine::assertFact(CVC5_UNUSED TNode atom,
                                     CVC5_UNUSED bool pol,
                                     TNode fact)
{
  d_core->assertFact(fact);
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

Node Z3QuantifiersEngine::getSkolemization(TNode q)
{
  // The lemma is made once per user context, while the core asserts it again
  // each time q is assigned false after a backtrack.
  theory::quantifiers::Skolemize* sk = d_qim.getSkolemize();
  sk->process(q);
  Node lem = sk->getSkolemizationLemma(q);
  Assert(!lem.isNull());
  return lem;
}

}  // namespace z3
}  // namespace cvc5::internal
