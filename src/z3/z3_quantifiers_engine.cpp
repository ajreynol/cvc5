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

#include "base/modal_exception.h"
#include "theory/output_channel.h"
#include "theory/quantifiers/theory_quantifiers.h"
#include "theory/theory_engine.h"
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

void Z3QuantifiersEngine::resetCore(TheoryEngine* te)
{
  d_backend.resetContext();
  d_core->reset(te);
}

Z3QuantifiersEngine::~Z3QuantifiersEngine() {}

Z3QuantifiersEngine* Z3QuantifiersEngine::get(TheoryEngine* te)
{
  return static_cast<Z3QuantifiersEngine*>(
      static_cast<theory::quantifiers::TheoryQuantifiers*>(
          te->theoryOf(theory::THEORY_QUANTIFIERS))
          ->getOwnedQuantifiersEngine());
}

void Z3QuantifiersEngine::finishInit(TheoryEngine* te)
{
  d_tracker = std::make_unique<RelevancyTracker>(d_env, te, *d_core);
  te->addModule(d_tracker.get());
}

const context::CDList<Node>* Z3QuantifiersEngine::getAssertedLiterals() const
{
  return d_tracker == nullptr ? nullptr : &d_tracker->getFacts();
}

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
    // the literals asserted since the last check, then the core
    d_tracker->flush(d_qstate);
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
                                     CVC5_UNUSED TNode fact)
{
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

void Z3QuantifiersEngine::unsupported(const char* what)
{
  std::stringstream ss;
  ss << what << " are not supported with --z3";
  throw ModalException(ss.str());
}

void Z3QuantifiersEngine::getInstantiatedQuantifiedFormulas(
    CVC5_UNUSED std::vector<Node>& qs)
{
  unsupported("instantiations");
}

void Z3QuantifiersEngine::getInstantiationTermVectors(
    CVC5_UNUSED Node q, CVC5_UNUSED std::vector<std::vector<Node>>& tvecs)
{
  unsupported("instantiations");
}

void Z3QuantifiersEngine::getInstantiationTermVectors(
    CVC5_UNUSED std::map<Node, std::vector<std::vector<Node>>>& insts)
{
  unsupported("instantiations");
}

void Z3QuantifiersEngine::getInstantiations(CVC5_UNUSED Node q,
                                            CVC5_UNUSED std::vector<Node>& insts)
{
  unsupported("instantiations");
}

void Z3QuantifiersEngine::getSkolemTermVectors(
    CVC5_UNUSED std::map<Node, std::vector<Node>>& sks) const
{
  unsupported("instantiations");
}

void Z3QuantifiersEngine::declarePool(
    CVC5_UNUSED Node p, CVC5_UNUSED const std::vector<Node>& initValue)
{
  unsupported("term pools");
}

void Z3QuantifiersEngine::declareOracleFun(CVC5_UNUSED Node f)
{
  unsupported("oracle functions");
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
