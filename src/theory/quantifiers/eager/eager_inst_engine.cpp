/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Eager E-matching, driven by notifications from the master equality engine.
 */

#include "theory/quantifiers/eager/eager_inst_engine.h"

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_util.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

void EagerEqNotify::eqNotifyNewClass(TNode t) { d_engine.notifyNewClass(t); }

void EagerEqNotify::eqNotifyMerge(TNode t1, TNode t2)
{
  d_engine.notifyMerge(t1, t2);
}

void EagerEqNotify::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  d_engine.notifyDisequal(t1, t2, reason);
}

EagerInstEngine::EagerInstEngine(Env& env,
                                 QuantifiersState& qs,
                                 QuantifiersInferenceManager& qim,
                                 QuantifiersRegistry& qr,
                                 TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_notify(*this),
      d_egraph(env, d_trail),
      d_mam(env, d_egraph, d_trail, options().quantifiers.eagerInstFilters),
      d_lazyMam(env, d_egraph, d_trail, options().quantifiers.eagerInstFilters),
      d_patInfer(env),
      d_queue(env, d_trail),
      d_inner(env, d_trail, qs),
      d_trailLevel(0),
      d_numLazyMatches(0),
      d_outputLemmas(options().quantifiers.eagerInstOutput
                     == options::EagerInstOutputMode::LEMMA),
      d_matchOnNotify(options().quantifiers.eagerInstMatchMode
                      == options::EagerInstMatchMode::NOTIFY)
{
  // The e-graph feeds the eager matcher. z3 additionally feeds the lazy
  // matcher, but only for the label maintenance (relevant_eh with lazy=true),
  // which here is done once by the e-graph for both.
  d_egraph.setListener(&d_mam);
  d_mam.setListener(&d_queue);
  d_lazyMam.setListener(&d_queue);
  d_queue.setSink(d_outputLemmas ? static_cast<InstanceSink*>(this)
                                 : static_cast<InstanceSink*>(&d_inner));
}

EagerInstEngine::~EagerInstEngine() {}

void EagerInstEngine::presolve() { syncScopes(); }

void EagerInstEngine::syncScopes()
{
  size_t level = static_cast<size_t>(context()->getLevel());
  if (level == d_trailLevel)
  {
    return;
  }
  if (level < d_trailLevel)
  {
    // z3's pop_scope additionally drops the pending matching work and the
    // pending instances
    d_mam.clearWork();
    d_lazyMam.clearWork();
    d_queue.clearWork();
    d_trail.popScope(d_trailLevel - level);
  }
  else
  {
    for (size_t i = d_trailLevel; i < level; i++)
    {
      d_trail.pushScope();
    }
  }
  d_trailLevel = level;
  Trace("eager-inst-debug") << "EagerInst: now at level " << level << std::endl;
}

void EagerInstEngine::notifyNewClass(TNode t)
{
  syncScopes();
  d_egraph.addTerm(t);
  if (d_matchOnNotify && d_mam.hasWork())
  {
    d_mam.match();
  }
}

void EagerInstEngine::notifyMerge(TNode t1, TNode t2)
{
  syncScopes();
  d_egraph.assertEq(t1, t2);
  if (d_matchOnNotify && d_mam.hasWork())
  {
    d_mam.match();
  }
}

void EagerInstEngine::notifyDisequal(TNode t1, TNode t2, TNode reason)
{
  syncScopes();
  d_egraph.assertDiseq(t1, t2, reason);
}

void EagerInstEngine::getPatterns(TNode q, std::vector<Node>& pats) const
{
  if (q.getNumChildren() != 3)
  {
    return;
  }
  for (const Node& p : q[2])
  {
    if (p.getKind() == Kind::INST_PATTERN)
    {
      pats.push_back(p);
    }
  }
}

void EagerInstEngine::assertNode(Node q)
{
  syncScopes();
  Assert(q.getKind() == Kind::FORALL);
  if (!d_asserted.insert(q).second)
  {
    return;
  }
  if (TermUtil::hasInstConstAttr(q))
  {
    // the inst-constant form of a quantified formula, which is a device of
    // counterexample-guided instantiation rather than an asserted formula
    Trace("eager-inst") << "EagerInst: skip inst-constant quantifier " << q
                        << std::endl;
    return;
  }
  if (!d_qreg.hasOwnership(q, this))
  {
    // Another module is responsible for this quantified formula and may claim
    // to be complete for it, which it would not be if we instantiated it too.
    // cvc5's lazy E-matching skips the same quantifiers
    // (InstantiationEngine::shouldProcess). z3 has no such notion, since it has
    // one instantiation mechanism.
    Trace("eager-inst") << "EagerInst: skip " << q
                        << ", owned by another module" << std::endl;
    return;
  }
  Node qn = q;
  d_trail.onPop([this, qn]() { d_asserted.erase(qn); });
  if (TraceIsOn("eager-inst-match"))
  {
    Node name = d_qreg.getQuantAttributes().getQuantName(q);
    Trace("eager-inst-match")
        << "QUANT " << q.getId() << " "
        << (name.isNull() ? std::string("?") : name.getName()) << std::endl;
  }
  std::vector<Node> pats;
  getPatterns(q, pats);
  if (pats.empty())
  {
    // z3: pattern_inference_cfg::reduce_quantifier, which runs during
    // preprocessing for the quantifiers that carry no pattern annotation
    d_patInfer.getPatterns(q, pats);
  }
  if (pats.empty())
  {
    Trace("eager-inst") << "EagerInst: no patterns for " << q << std::endl;
    return;
  }
  // z3: default_qm_plugin::assign_eh. Unary patterns and the first
  // qi.max_eager_multipatterns multi-patterns are matched eagerly, the rest
  // only at final check.
  bool hasUnaryPattern = false;
  for (const Node& mp : pats)
  {
    if (mp.getNumChildren() == 1)
    {
      hasUnaryPattern = true;
      break;
    }
  }
  uint32_t numEagerMulti = options().quantifiers.eagerInstMaxEagerMultipatterns;
  if (!hasUnaryPattern)
  {
    numEagerMulti++;
  }
  uint32_t j = 0;
  for (const Node& mp : pats)
  {
    bool unary = mp.getNumChildren() == 1;
    if (!unary && j >= numEagerMulti)
    {
      d_lazyMam.addPattern(q, mp);
    }
    else
    {
      d_mam.addPattern(q, mp);
    }
    if (!unary)
    {
      j++;
    }
  }
}

void EagerInstEngine::propagate(CVC5_UNUSED Theory::Effort e)
{
  // z3: quantifier_manager::imp::propagate, which runs the matcher and then
  // turns the matches it reported into instances
  syncScopes();
  if (d_mam.hasWork())
  {
    d_mam.match();
  }
  if (d_queue.hasWork())
  {
    d_queue.instantiate();
  }
}

void EagerInstEngine::flush(CVC5_UNUSED Theory::Effort e)
{
  syncScopes();
  bool ok = d_inner.check();
  // Whatever the inner solver exports has the effect of instantiating the
  // quantified formulas whose instances it used, so cvc5's bookkeeping is told
  // about them; otherwise a module that is responsible for one of them builds
  // its model as if it had not been instantiated.
  Instantiate* inst = d_qim.getInstantiate();
  const std::vector<std::pair<Node, std::vector<Node>>>& used =
      d_inner.getUsedInstantiations();
  if (used.size() == 1)
  {
    // The clause follows from a single instance, so it is subsumed by that
    // instantiation. Going through Instantiate rather than sending the clause
    // directly keeps cvc5's instantiation bookkeeping, rewriting and proof
    // support in play.
    std::vector<Node> terms = used[0].second;
    Trace("eager-inst") << "EagerInst: instantiate " << used[0].first
                        << std::endl;
    inst->addInstantiation(
        used[0].first, terms, InferenceId::QUANTIFIERS_INST_E_MATCHING_EAGER);
    d_inner.clearPropagations();
    traceStats();
    return;
  }
  for (const std::pair<Node, std::vector<Node>>& ui : used)
  {
    if (!inst->existsInstantiation(ui.first, ui.second))
    {
      inst->recordInstantiation(ui.first, ui.second);
    }
  }
  if (!ok)
  {
    Node conf = d_inner.getConflict();
    Assert(!conf.isNull());
    Trace("eager-inst") << "EagerInst: inner conflict " << conf << std::endl;
    d_qim.addPendingLemma(conf, InferenceId::QUANTIFIERS_INST_E_MATCHING_EAGER);
  }
  for (const std::pair<Node, Node>& p : d_inner.getPropagations())
  {
    Trace("eager-inst") << "EagerInst: inner propagation " << p.first
                        << " from " << p.second << std::endl;
    d_qim.addPendingLemma(p.second.impNode(p.first),
                          InferenceId::QUANTIFIERS_INST_E_MATCHING_EAGER);
  }
  d_inner.clearPropagations();
  traceStats();
}

void EagerInstEngine::check(Theory::Effort e, QEffort quantE)
{
  if (quantE != QEFFORT_STANDARD)
  {
    return;
  }
  syncScopes();
  propagate(e);
  if (e >= Theory::EFFORT_LAST_CALL)
  {
    // z3: qi_queue::final_check_eh followed by
    // default_qm_plugin::final_check_quant, which rematches the patterns that
    // were not matched eagerly, at most qi.max_lazy_multipattern_matching
    // times.
    d_queue.finalCheck();
    if (d_numLazyMatches
        < options().quantifiers.eagerInstMaxLazyMultipatternMatching)
    {
      d_numLazyMatches++;
      d_lazyMam.rematch();
      d_queue.instantiate();
    }
  }
}

void EagerInstEngine::addInstance(CVC5_UNUSED TNode q,
                                  CVC5_UNUSED const std::vector<Node>& terms,
                                  TNode lemma,
                                  CVC5_UNUSED uint32_t generation)
{
  // the bring-up path, --eager-inst-output=lemma
  d_qim.addPendingLemma(lemma, InferenceId::QUANTIFIERS_INST_E_MATCHING_EAGER);
}

void EagerInstEngine::traceStats() const
{
  const Mam::Stats& ms = d_mam.getStats();
  const InstQueue::Stats& qs = d_queue.getStats();
  const InnerSmtSolver::Stats& is = d_inner.getStats();
  Trace("eager-inst-stats")
      << "EagerInst: " << d_egraph.getNumENodes() << " enodes, "
      << ms.d_numMerges << " merges, " << ms.d_numCandidates << " candidates, "
      << ms.d_numMatchCalls << " match calls, " << ms.d_numMatches
      << " matches; queue: " << qs.d_numMatches << " in, " << qs.d_numDuplicates
      << " duplicates, " << qs.d_numInstances << " instances, "
      << qs.d_numLazyInstances << " lazy, " << qs.d_numTrivial
      << " trivial; inner: " << is.d_numInstances << " added, "
      << is.d_numRetracted << " retracted, " << is.d_numChecks << " checks, "
      << is.d_numConflicts << " conflicts" << std::endl;
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
