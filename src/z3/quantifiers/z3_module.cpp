/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The quantifiers module of the ported Z3 core.
 */

#include "z3/quantifiers/z3_module.h"

#include <ctime>

#include "options/base_options.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/skolemize.h"
#include "theory/theory_engine.h"
#include "z3/quantifiers/shadow_feed.h"
#include "z3/quantifiers/smt_context.h"

namespace cvc5::internal {
namespace z3 {

Z3Module::Z3Module(Env& env,
                   theory::quantifiers::QuantifiersState& qs,
                   theory::quantifiers::QuantifiersInferenceManager& qim,
                   theory::quantifiers::QuantifiersRegistry& qr,
                   theory::quantifiers::TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr)
{
}

Z3Module::~Z3Module() {}

void Z3Module::finishInit(TheoryEngine* te)
{
  // The core sends its lemmas through the inference manager, with their
  // inferences; the instances it sends again are local to the SAT context,
  // which the inference manager does not cache (see HostCore::reset).
  d_core = std::make_unique<HostCore>(
      d_env, d_qim, [this](TNode q) { return getSkolemization(q); });
  d_core->reset(te);
  d_tracker = std::make_unique<RelevancyTracker>(
      d_env, te, [this](TNode lit) { d_core->assertFact(lit); });
  te->addModule(d_tracker.get());
}

TrustNode Z3Module::getSkolemization(TNode q)
{
  // The lemma is made once per user context, by the quantifiers engine when
  // q is asserted false (or here, for a quantified formula it reduced), while
  // the core asserts it again each time q is assigned false after a
  // backtrack.
  theory::quantifiers::Skolemize* sk = d_qim.getSkolemize();
  sk->process(q);
  TrustNode lem = sk->getSkolemizationLemma(q);
  Assert(!lem.isNull());
  return lem;
}

void Z3Module::presolve()
{
  d_core->getShadowFeed()->setMasterEqualityEngine(
      d_qstate.getEqualityEngine());
  d_core->presolve();
}

void Z3Module::ppNotifyAssertions(const std::vector<Node>& assertions)
{
  d_core->assertInput(assertions);
}

bool Z3Module::needsCheck(theory::Theory::Effort e)
{
  return e != theory::Theory::EFFORT_LAST_CALL;
}

void Z3Module::check(theory::Theory::Effort e, QEffort quant_e)
{
  // once per check of the quantifiers engine
  if (quant_e != QEFFORT_STANDARD)
  {
    return;
  }
  // -o inst-strategy prints a line per call that made instances, as for the
  // other modules, which count them through the inference manager; the core
  // sends its instances itself, and counts them. It is called at every
  // standard effort check, most of which make none.
  bool printing = isOutputOn(OutputTag::INST_STRATEGY);
  const Statistics& stats = d_core->getContext().getStats();
  uint64_t numInstances = stats.d_numInstances;
  clock_t start = printing ? clock() : 0;
  // the literals asserted since the last check, then the core
  d_tracker->flush(d_qstate);
  d_core->check(e);
  if (printing && stats.d_numInstances > numInstances)
  {
    double time = static_cast<double>(clock() - start)
                  / static_cast<double>(CLOCKS_PER_SEC);
    std::ostream& out = output(OutputTag::INST_STRATEGY);
    out << "(inst-strategy " << identify();
    out << " :inst " << (stats.d_numInstances - numInstances);
    out << " :time " << time;
    if (d_qstate.isInConflict())
    {
      out << " :conflict";
    }
    out << ")" << std::endl;
  }
}

void Z3Module::preRegisterQuantifier(Node q)
{
  // The core takes the atoms of the SAT solver; it internalizes the terms
  // under them itself.
  if (d_qstate.getValuation().isSatLiteral(q))
  {
    d_core->preRegister(q);
  }
}

void Z3Module::notifyMasterMerge(TNode t1, TNode t2)
{
  d_core->getShadowFeed()->eqNotifyMerge(t1, t2);
}

}  // namespace z3
}  // namespace cvc5::internal
