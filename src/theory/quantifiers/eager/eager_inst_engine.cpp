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
      d_trailLevel(0),
      d_syncedLevel(context(), 0),
      d_numLazyMatches(0),
      d_outputLemmas(options().quantifiers.eagerInstOutput
                     == options::EagerInstOutputMode::LEMMA),
      d_outputInst(options().quantifiers.eagerInstOutput
                   == options::EagerInstOutputMode::INST),
      d_matchOnNotify(options().quantifiers.eagerInstMatchMode
                      == options::EagerInstMatchMode::NOTIFY),
      d_relevantOnly(options().quantifiers.eagerInstRelevant),
      d_factCursor(context()),
      d_maxContributions(options().quantifiers.eagerInstMaxContributions),
      d_numContributed(0)
{
  // The e-graph feeds the eager matcher. z3 additionally feeds the lazy
  // matcher, but only for the label maintenance (relevant_eh with lazy=true),
  // which here is done once by the e-graph for both.
  d_egraph.addListener(&d_mam);
  d_mam.setListener(&d_queue);
  d_lazyMam.setListener(&d_queue);
  if (d_relevantOnly)
  {
    d_egraph.setCandidateGating(true);
  }
  d_useInner = options().quantifiers.eagerInstOutput
               == options::EagerInstOutputMode::INNER;
  if (d_useInner)
  {
    d_inner.reset(new InnerSmtSolver(env, d_trail, qs, d_egraph));
    d_inner->setInstantiate(d_qim.getInstantiate());
    // the inner solver follows the outer classes of its terms, and is the only
    // consumer of the disequalities
    d_egraph.addListener(d_inner.get());
    d_egraph.setTrackDisequalities(true);
  }
  // With no sink the instances are discarded once they have been found, which
  // isolates the cost of matching from the cost of what is done with them.
  d_queue.setSink(d_useInner ? static_cast<InstanceSink*>(d_inner.get())
                             : ((d_outputLemmas || d_outputInst)
                                    ? static_cast<InstanceSink*>(this)
                                    : nullptr));
}

EagerInstEngine::~EagerInstEngine() {}

void EagerInstEngine::presolve() { syncScopes(); }

void EagerInstEngine::syncScopes()
{
  size_t level = static_cast<size_t>(context()->getLevel());
  // The scopes of our trail above the last level synced at that the context
  // still has were popped by the context, even if it has pushed back to the
  // same level since.
  size_t valid = std::min(level, d_syncedLevel.get());
  if (level == d_trailLevel && valid == d_trailLevel)
  {
    return;
  }
  if (valid < d_trailLevel)
  {
    // z3's pop_scope additionally drops the pending matching work and the
    // pending instances
    d_mam.clearWork();
    d_lazyMam.clearWork();
    d_queue.clearWork();
    d_pendingInsts.clear();
    d_trail.popScope(d_trailLevel - valid);
    d_trailLevel = valid;
  }
  for (size_t i = d_trailLevel; i < level; i++)
  {
    d_trail.pushScope();
  }
  d_trailLevel = level;
  d_syncedLevel = level;
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
  // Ownership is deliberately not consulted. This module never takes ownership
  // of a quantified formula and never claims to be complete for one: it only
  // contributes instantiations that are already contradictory, and only at
  // conflict effort or earlier, so it never stops the module that is
  // responsible for a quantified formula from doing its own job.
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

void EagerInstEngine::sweepFacts()
{
  const LogicInfo& logicInfo = d_qstate.getLogicInfo();
  for (TheoryId tid = THEORY_FIRST; tid < THEORY_LAST; ++tid)
  {
    if (!logicInfo.isTheoryEnabled(tid))
    {
      continue;
    }
    context::CDList<Assertion>::const_iterator begin = d_qstate.factsBegin(tid);
    size_t n = static_cast<size_t>(d_qstate.factsEnd(tid) - begin);
    uint32_t key = static_cast<uint32_t>(tid);
    context::CDHashMap<uint32_t, size_t>::const_iterator itc =
        d_factCursor.find(key);
    size_t i = itc == d_factCursor.end() ? 0 : (*itc).second;
    if (i >= n)
    {
      // the list shrank with a pop, or there is nothing new
      continue;
    }
    for (; i < n; i++)
    {
      d_egraph.markRelevant((*(begin + i)).d_assertion);
    }
    d_factCursor[key] = n;
  }
}

void EagerInstEngine::propagate(CVC5_UNUSED Theory::Effort e)
{
  // z3: quantifier_manager::imp::propagate, which runs the matcher and then
  // turns the matches it reported into instances
  syncScopes();
  if (d_relevantOnly)
  {
    sweepFacts();
  }
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
  if (d_useInner)
  {
    flushInner();
  }
  else
  {
    flushInstances();
  }
  traceStats();
}

void EagerInstEngine::flushInstances()
{
  if (d_pendingInsts.empty())
  {
    return;
  }
  // The instances the matcher found become instantiations of their quantified
  // formulas. This is how z3 closes the loop: an instance is asserted, its
  // terms are internalized into the e-graph, and the matcher sees them, so one
  // instance can lead to the next. Going through Instantiate rather than
  // sending the clause keeps cvc5's duplicate filter, rewriting, proofs and
  // bookkeeping in play, and means the module responsible for a quantified
  // formula knows that it has been instantiated.
  Instantiate* inst = d_qim.getInstantiate();
  std::vector<PendingInst> pending;
  pending.swap(d_pendingInsts);
  for (PendingInst& pi : pending)
  {
    if (!mayContribute())
    {
      break;
    }
    // We are outside of a round of instantiation, where the term database that
    // the entailment check relies on is stale, so that check is skipped.
    if (inst->addInstantiation(pi.d_quant,
                               pi.d_terms,
                               InferenceId::QUANTIFIERS_INST_E_MATCHING_EAGER,
                               Node::null(),
                               false,
                               false))
    {
      d_numContributed++;
      Trace("eager-inst") << "EagerInst: instantiate " << pi.d_quant
                          << std::endl;
    }
  }
}

void EagerInstEngine::flushInner()
{
  if (!mayContribute())
  {
    return;
  }
  syncScopes();
  bool ok = d_inner->check();
  // Whatever the inner solver exports has the effect of instantiating the
  // quantified formulas whose instances it used, so cvc5's bookkeeping is told
  // about them; otherwise a module that is responsible for one of them builds
  // its model as if it had not been instantiated.
  Instantiate* inst = d_qim.getInstantiate();
  const std::vector<std::pair<Node, std::vector<Node>>>& used =
      d_inner->getUsedInstantiations();
  if (used.size() == 1)
  {
    // The clause follows from a single instance, so it is subsumed by that
    // instantiation.
    std::vector<Node> terms = used[0].second;
    std::pair<Node, std::vector<Node>> key(used[0].first, terms);
    if (!d_emittedInst.insert(key).second)
    {
      // already contributed at this scope
      d_inner->clearPropagations();
      return;
    }
    d_trail.onPop([this, key]() { d_emittedInst.erase(key); });
    Trace("eager-inst") << "EagerInst: instantiate " << used[0].first
                        << std::endl;
    inst->addInstantiation(used[0].first,
                           terms,
                           InferenceId::QUANTIFIERS_INST_E_MATCHING_EAGER,
                           Node::null(),
                           false,
                           false);
    d_numContributed++;
    // cvc5 owns this instance now
    d_inner->deactivateUsedInstances();
    d_inner->clearPropagations();
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
    Node conf = d_inner->getConflict();
    Assert(!conf.isNull());
    if (d_emittedConflict.insert(conf).second)
    {
      Node confn = conf;
      d_trail.onPop([this, confn]() { d_emittedConflict.erase(confn); });
      Trace("eager-inst") << "EagerInst: inner conflict " << conf << std::endl;
      d_qim.addPendingLemma(conf,
                            InferenceId::QUANTIFIERS_INST_E_MATCHING_EAGER);
      d_numContributed++;
      // the instances the conflict used have been handed over
      d_inner->deactivateUsedInstances();
    }
  }
  for (const std::pair<Node, Node>& p : d_inner->getPropagations())
  {
    Trace("eager-inst") << "EagerInst: inner propagation " << p.first
                        << " from " << p.second << std::endl;
    d_qim.addPendingLemma(p.second.impNode(p.first),
                          InferenceId::QUANTIFIERS_INST_E_MATCHING_EAGER);
  }
  d_inner->clearPropagations();
}

bool EagerInstEngine::needsCheck(Theory::Effort e)
{
  // Conflict effort is where this module contributes, as QuantConflictFind
  // does, which also only reports conflicts.
  return e >= Theory::EFFORT_FULL;
}

void EagerInstEngine::check(Theory::Effort e, QEffort quantE)
{
  if (quantE == QEFFORT_CONFLICT)
  {
    // Instantiations are contributed here, at conflict effort, so that they are
    // seen before the module responsible for a quantified formula acts on it,
    // and never afterwards.
    syncScopes();
    propagate(e);
    flush(e);
    return;
  }
  if (quantE != QEFFORT_STANDARD)
  {
    return;
  }
  syncScopes();
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

void EagerInstEngine::addInstance(TNode q,
                                  const std::vector<Node>& terms,
                                  TNode lemma,
                                  uint32_t generation)
{
  if (d_outputLemmas)
  {
    // the bring-up path, --eager-inst-output=lemma
    d_qim.addPendingLemma(lemma,
                          InferenceId::QUANTIFIERS_INST_E_MATCHING_EAGER);
    return;
  }
  // The terms of the instance reach the e-graph later, when cvc5 has processed
  // the instantiation and they become relevant, so the generation they belong
  // to is registered now.
  d_egraph.registerGeneration(lemma, generation);
  d_pendingInsts.push_back(PendingInst{q, terms});
}

void EagerInstEngine::traceStats() const
{
  if (!TraceIsOn("eager-inst-stats"))
  {
    return;
  }
  const Mam::Stats& ms = d_mam.getStats();
  const InstQueue::Stats& qs = d_queue.getStats();
  Trace("eager-inst-stats")
      << "EagerInst: " << d_egraph.getNumENodes() << " enodes ("
      << d_egraph.getNumCandidateENodes() << " matchable), "
      << ms.d_numMerges << " merges, " << ms.d_numCandidates << " candidates, "
      << ms.d_numMatchCalls << " match calls, " << ms.d_numMatches
      << " matches; queue: " << qs.d_numMatches << " in, " << qs.d_numDuplicates
      << " duplicates, " << qs.d_numInstances << " instances, "
      << qs.d_numLazyInstances << " lazy, " << qs.d_numTrivial
      << " trivial; added " << d_numContributed;
  if (d_inner != nullptr)
  {
    const InnerSmtSolver::Stats& is = d_inner->getStats();
    Trace("eager-inst-stats")
        << "; inner: " << is.d_numInstances << " added, " << is.d_numRetracted
        << " retracted, " << is.d_numChecks << " checks, " << is.d_numConflicts
        << " conflicts; search: " << is.d_numDecisions << " decisions, "
        << is.d_numSearchConflicts << " backjumps, " << is.d_numSaturated
        << " saturated, " << is.d_numBudgetOut << " budget-out, "
        << is.d_numOuterFacts << " outer facts, " << is.d_numAlreadyKnown
        << " already known, " << is.d_numDeactivated << " handed off";
  }
  Trace("eager-inst-stats") << std::endl;
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
