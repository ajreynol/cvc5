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

#include "z3/z3_theory_engine.h"

#include "proof/trust_node.h"
#include "prop/prop_engine.h"
#include "theory/inference_id.h"

namespace cvc5::internal {
namespace z3 {

Z3TheoryEngine::Z3TheoryEngine(Env& env, bool hosted)
    : TheoryEngine(env), d_backend(env), d_hosted(hosted), d_output(*this)
{
  if (d_hosted)
  {
    d_core = std::make_unique<HostCore>(env, d_backend, *this, d_output);
  }
}

Z3TheoryEngine::~Z3TheoryEngine() {}

void Z3TheoryEngine::preRegister(TNode atom)
{
  if (!d_hosted)
  {
    TheoryEngine::preRegister(atom);
    return;
  }
  d_core->preRegister(atom);
}

void Z3TheoryEngine::assertFact(TNode literal)
{
  if (!d_hosted)
  {
    TheoryEngine::assertFact(literal);
    return;
  }
  d_core->assertFact(literal);
}

void Z3TheoryEngine::check(theory::Theory::Effort effort)
{
  if (!d_hosted)
  {
    TheoryEngine::check(effort);
    return;
  }
  // cvc5 has taken the propagations of the previous check
  d_propagations.clear();
  d_core->check(effort);
}

bool Z3TheoryEngine::presolve()
{
  if (!d_hosted)
  {
    return TheoryEngine::presolve();
  }
  d_core->presolve();
  return false;
}

void Z3TheoryEngine::postsolve(prop::SatValue result)
{
  if (!d_hosted)
  {
    TheoryEngine::postsolve(result);
  }
}

void Z3TheoryEngine::notifyRestart()
{
  if (!d_hosted)
  {
    TheoryEngine::notifyRestart();
  }
}

void Z3TheoryEngine::getPropagatedLiterals(std::vector<TNode>& literals)
{
  if (!d_hosted)
  {
    TheoryEngine::getPropagatedLiterals(literals);
    return;
  }
  // d_propagations keeps the nodes alive until the next check
  literals.insert(literals.end(), d_propagations.begin(), d_propagations.end());
}

Node Z3TheoryEngine::getNextDecisionRequest()
{
  if (!d_hosted)
  {
    return TheoryEngine::getNextDecisionRequest();
  }
  return Node::null();
}

TrustNode Z3TheoryEngine::getExplanation(TNode literal)
{
  if (!d_hosted)
  {
    return TheoryEngine::getExplanation(literal);
  }
  return TrustNode::mkTrustPropExp(literal, d_core->explain(literal), nullptr);
}

bool Z3TheoryEngine::needCheck() const
{
  if (!d_hosted)
  {
    return TheoryEngine::needCheck();
  }
  return d_core->needCheck();
}

void Z3TheoryEngine::Output::lemma(const Node& lem,
                                   theory::LemmaProperty p,
                                   bool notifyDecisions)
{
  d_te.getPropEngine()->assertLemmaUnprocessed(theory::InferenceId::UNKNOWN,
                                               TrustNode::mkTrustLemma(lem),
                                               p,
                                               notifyDecisions);
}

void Z3TheoryEngine::Output::propagate(const Node& lit)
{
  d_te.d_propagations.push_back(lit);
}

void Z3TheoryEngine::Output::preferPhase(TNode atom, bool phase)
{
  d_te.getPropEngine()->preferPhase(atom, phase);
}

void Z3TheoryEngine::Output::setModelUnsound(theory::IncompleteId id)
{
  d_te.setModelUnsound(id);
}

}  // namespace z3
}  // namespace cvc5::internal
