/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Eager instantiation via E-matching on new terms.
 */

#include "theory/quantifiers/eager_inst.h"

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/uf/equality_engine.h"
#include "util/resource_manager.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

EagerInstantiation::EagerTrigger::EagerTrigger(
    context::Context* c,
    const Node& q,
    const Node& pattern,
    const std::vector<Node>& otherPatterns)
    : d_quant(q),
      d_pattern(pattern),
      d_otherPatterns(otherPatterns),
      d_procIdx(c, 0),
      d_roundStamp(0),
      d_roundActive(false)
{
  for (size_t i = 0, nchild = pattern.getNumChildren(); i < nchild; i++)
  {
    if (!expr::hasBoundVar(pattern[i]))
    {
      d_groundPos.push_back(i);
    }
  }
}

EagerInstantiation::EagerInstantiation(Env& env,
                                       QuantifiersState& qs,
                                       QuantifiersInferenceManager& qim,
                                       QuantifiersRegistry& qr,
                                       TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_activeQuants(context()),
      d_sentFps(context()),
      d_rlvTerms(context()),
      d_mergeQueue(context()),
      d_mergeIdx(context(), 0),
      d_round(0),
      d_procTime(statisticsRegistry().registerTimer(
          "theory::quantifiers::eagerInst::processTime")),
      d_addInstTime(statisticsRegistry().registerTimer(
          "theory::quantifiers::eagerInst::addInstTime")),
      d_statPairs(statisticsRegistry().registerInt(
          "theory::quantifiers::eagerInst::numPairsProcessed")),
      d_statMatches(statisticsRegistry().registerInt(
          "theory::quantifiers::eagerInst::numMatches")),
      d_statInst(statisticsRegistry().registerInt(
          "theory::quantifiers::eagerInst::numInstantiations")),
      d_statRematch(statisticsRegistry().registerInt(
          "theory::quantifiers::eagerInst::numTermsRematched"))
{
}

EagerInstantiation::~EagerInstantiation() {}

bool EagerInstantiation::needsCheck(Theory::Effort e)
{
  if (e != Theory::EFFORT_FULL)
  {
    // We process new terms at standard effort via a direct call to
    // processNewTerms from the quantifiers engine. We only require a check
    // at full effort if there are still unprocessed pairs, e.g. if the
    // previous standard effort check was interrupted by a conflict or
    // stopped due to the instantiation limit.
    return false;
  }
  if ((options().quantifiers.eagerInstMerge
       || options().quantifiers.eagerInstRlv)
      && d_mergeIdx.get() < d_mergeQueue.size())
  {
    return true;
  }
  for (const std::pair<const Node, std::vector<std::unique_ptr<EagerTrigger>>>&
           ot : d_opTriggers)
  {
    std::map<Node, std::unique_ptr<OpTermList>>::iterator itt =
        d_opTerms.find(ot.first);
    if (itt == d_opTerms.end())
    {
      continue;
    }
    size_t nuniq = itt->second->d_unique.size();
    // whether promotion may extend the unique list
    bool promotionPending =
        itt->second->d_rawIdx.get() < itt->second->d_list.size();
    for (const std::unique_ptr<EagerTrigger>& tr : ot.second)
    {
      if ((promotionPending || tr->d_procIdx.get() < nuniq)
          && d_activeQuants.contains(tr->d_quant))
      {
        return true;
      }
    }
  }
  return false;
}

void EagerInstantiation::check(CVC5_UNUSED Theory::Effort e, QEffort quant_e)
{
  if (quant_e != QEFFORT_CONFLICT)
  {
    return;
  }
  processNewTerms();
}

void EagerInstantiation::registerQuantifier(Node q)
{
  if (q.getNumChildren() != 3)
  {
    return;
  }
  // We process quantified formulas that are unowned, or owned by the lazy
  // instantiation engine, which takes ownership of quantified formulas with
  // user patterns when --user-pat=strict. Eager and lazy E-matching are
  // complementary strategies over the same triggers.
  QuantifiersModule* owner = d_qreg.getOwner(q);
  if (owner != nullptr && owner != this && owner != d_instEngine)
  {
    Trace("eager-inst-reject")
        << "Eager inst: reject (owner=" << owner->identify() << ") " << q
        << std::endl;
    return;
  }
  // collect the variables of q
  std::unordered_set<Node> qvars(q[0].begin(), q[0].end());
  for (const Node& ipl : q[2])
  {
    if (ipl.getKind() != Kind::INST_PATTERN || ipl.getNumChildren() == 0)
    {
      continue;
    }
    if (ipl.getNumChildren() > 1 && !options().quantifiers.eagerInstMulti)
    {
      Trace("eager-inst-reject")
          << "Eager inst: reject multi-trigger (disabled) : " << ipl
          << std::endl;
      continue;
    }
    // all patterns must be applications of uninterpreted functions
    bool allUf = true;
    for (const Node& pat : ipl)
    {
      if (pat.getKind() != Kind::APPLY_UF)
      {
        Trace("eager-inst-reject")
            << "Eager inst: reject pattern kind " << pat.getKind() << " : "
            << pat << std::endl;
        allUf = false;
        break;
      }
    }
    if (!allUf)
    {
      continue;
    }
    // the patterns must contain all variables of q
    std::unordered_set<Node> fvs;
    for (const Node& pat : ipl)
    {
      expr::getFreeVariables(pat, fvs);
    }
    bool covers = true;
    for (const Node& v : qvars)
    {
      if (fvs.find(v) == fvs.end())
      {
        covers = false;
        break;
      }
    }
    if (!covers)
    {
      Trace("eager-inst-reject")
          << "Eager inst: reject pattern (does not cover vars) : " << ipl
          << std::endl;
      continue;
    }
    // For a multi-trigger, we register one trigger per focus pattern, so
    // that a new term with the operator of any of the patterns initiates
    // matching.
    for (size_t fi = 0, npats = ipl.getNumChildren(); fi < npats; fi++)
    {
      std::vector<Node> others;
      for (size_t j = 0; j < npats; j++)
      {
        if (j != fi)
        {
          others.push_back(ipl[j]);
        }
      }
      Node op = ipl[fi].getOperator();
      d_opTriggers[op].emplace_back(
          std::make_unique<EagerTrigger>(context(), q, ipl[fi], others));
      Trace("eager-inst") << "Eager inst: trigger for " << q << " : " << ipl[fi]
                          << (others.empty() ? "" : " (multi)") << std::endl;
    }
  }
}

void EagerInstantiation::assertNode(Node q)
{
  if (d_activeQuants.contains(q))
  {
    return;
  }
  d_activeQuants.insert(q);
  Trace("eager-inst") << "Eager inst: activate " << q << std::endl;
}

void EagerInstantiation::eqNotifyNewClass(TNode t)
{
  // We only consider applications of uninterpreted functions, which is the
  // only kind of pattern head we currently handle. Note we must not do any
  // matching here, since the equality engine may be mid-operation; we only
  // enqueue the term.
  if (t.getKind() == Kind::APPLY_UF)
  {
    getOpTermList(t.getOperator()).d_list.push_back(t);
    // register t in the parent index, once globally
    if (d_parentsRegistered.insert(t).second)
    {
      for (const Node& tc : t)
      {
        d_parents[tc].push_back(t);
      }
    }
  }
}

void EagerInstantiation::eqNotifyMerge(TNode t1, TNode t2)
{
  if (!options().quantifiers.eagerInstMerge
      && !options().quantifiers.eagerInstRlv)
  {
    return;
  }
  // Only enqueue; the merged terms are inspected at the next processing
  // round.
  d_mergeQueue.push_back(std::pair<Node, Node>(t1, t2));
}

EagerInstantiation::OpTermList& EagerInstantiation::getOpTermList(
    const Node& op)
{
  std::map<Node, std::unique_ptr<OpTermList>>::iterator it = d_opTerms.find(op);
  if (it == d_opTerms.end())
  {
    it = d_opTerms.emplace(op, std::make_unique<OpTermList>(context())).first;
  }
  return *it->second;
}

Node EagerInstantiation::computeSig(TNode t)
{
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  std::vector<Node> sigc;
  for (const Node& tc : t)
  {
    sigc.push_back(ee->getRepresentative(tc));
  }
  return nodeManager()->mkNode(Kind::SEXPR, sigc);
}

void EagerInstantiation::promoteTerms(OpTermList& ol)
{
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  size_t i = ol.d_rawIdx.get();
  size_t nterms = ol.d_list.size();
  if (i >= nterms)
  {
    return;
  }
  uint64_t genLimit = options().quantifiers.eagerInstGenLimit;
  bool rlv = options().quantifiers.eagerInstRlv;
  while (i < nterms)
  {
    TNode t = ol.d_list[i];
    i++;
    if (!ee->hasTerm(t))
    {
      // can happen if the term was removed by a backtrack after it was
      // queued
      continue;
    }
    if (rlv && !d_rlvTerms.contains(t))
    {
      Node r = ee->getRepresentative(t);
      if (r == t)
      {
        eq::EqClassIterator eqc(r, ee);
        ++eqc;
        if (eqc.isFinished())
        {
          // The term is in a singleton class and not marked relevant: the
          // search has not engaged it yet. Defer; it is re-enqueued when
          // it participates in a merge (processMerges).
          Trace("eager-inst-debug2")
              << "Eager inst: defer irrelevant " << t << std::endl;
          continue;
        }
      }
    }
    if (genLimit > 0)
    {
      std::unordered_map<Node, uint64_t>::iterator itg = d_termGen.find(t);
      if (itg != d_termGen.end() && itg->second >= genLimit)
      {
        // The term was introduced by a (deep) chain of eager
        // instantiations; do not match it eagerly. Instantiations
        // depending on it are found by the lazy engine.
        Trace("eager-inst-debug2") << "Eager inst: do not promote generation "
                                   << itg->second << " term " << t << std::endl;
        continue;
      }
    }
    // The signature of t is the tuple of representatives of its arguments
    // (its operator is implied by the list it occurs in). Note that within
    // a SAT context, congruences are never undone, so the promotion
    // decision remains valid for the lifetime of this list entry.
    Node sig = computeSig(t);
    if (!ol.d_sigs.contains(sig))
    {
      ol.d_sigs.insert(sig);
      ol.d_unique.push_back(t);
      ol.d_uniqueSigs.push_back(sig);
    }
    else
    {
      Trace("eager-inst-debug2")
          << "Eager inst: do not promote congruent " << t << std::endl;
    }
  }
  ol.d_rawIdx = i;
}

void EagerInstantiation::processMerges()
{
  size_t i = d_mergeIdx.get();
  size_t endIdx = d_mergeQueue.size();
  if (i >= endIdx)
  {
    return;
  }
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  bool doParents = options().quantifiers.eagerInstMerge;
  bool doRlv = options().quantifiers.eagerInstRlv;
  // The terms re-appended/activated this round, to avoid duplicate work
  // when a term is involved in several merges.
  std::unordered_set<Node> repushed;
  std::unordered_set<Node> activated;
  while (i < endIdx)
  {
    const std::pair<Node, Node>& m = d_mergeQueue[i];
    i++;
    for (size_t j = 0; j < 2; j++)
    {
      TNode u = j == 0 ? m.first : m.second;
      if (doRlv && activated.insert(u).second)
      {
        // The merge follows from an asserted literal (or a congruence
        // entailed by one), hence mark u and its APPLY_UF subterms
        // relevant and re-enqueue them for promotion, in case they were
        // previously deferred.
        std::unordered_set<Node> sub;
        expr::getSubtermsKind(Kind::APPLY_UF, u, sub);
        if (u.getKind() == Kind::APPLY_UF)
        {
          sub.insert(u);
        }
        for (const Node& s : sub)
        {
          if (!d_rlvTerms.contains(s))
          {
            d_rlvTerms.insert(s);
            getOpTermList(s.getOperator()).d_list.push_back(s);
          }
        }
      }
      if (!doParents)
      {
        continue;
      }
      // Re-append the parents of the two merged terms, with fresh
      // signatures, so that all triggers re-match them. Note we do not
      // consider the parents of the other members of the merged classes:
      // congruences propagated by the merge generate their own merge
      // notifications, which covers the parents of congruent members.
      // Matches that become possible for a parent of another member of the
      // merged classes (via deep matching into the grown class) are missed
      // here; these are found by the lazy instantiation engine.
      std::map<Node, std::vector<Node>>::iterator itp = d_parents.find(u);
      if (itp == d_parents.end())
      {
        continue;
      }
      for (const Node& p : itp->second)
      {
        if (!repushed.insert(p).second)
        {
          continue;
        }
        if (!ee->hasTerm(p))
        {
          continue;
        }
        // only re-append if some trigger may consider it
        Node pop = p.getOperator();
        if (d_opTriggers.find(pop) == d_opTriggers.end())
        {
          continue;
        }
        Trace("eager-inst-debug") << "Eager inst: re-match " << p
                                  << " due to merge on " << u << std::endl;
        OpTermList& ol = getOpTermList(pop);
        ol.d_unique.push_back(p);
        ol.d_uniqueSigs.push_back(computeSig(p));
        ++d_statRematch;
      }
    }
  }
  d_mergeIdx = i;
}

void EagerInstantiation::refreshTriggerCache(EagerTrigger& tr)
{
  if (tr.d_roundStamp == d_round)
  {
    return;
  }
  tr.d_roundStamp = d_round;
  tr.d_roundActive = true;
  tr.d_groundReps.clear();
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  for (size_t pos : tr.d_groundPos)
  {
    TNode g = tr.d_pattern[pos];
    if (!ee->hasTerm(g))
    {
      // a ground argument of the pattern does not occur in the equality
      // engine, hence the pattern cannot match this round
      tr.d_roundActive = false;
      return;
    }
    tr.d_groundReps.push_back(ee->getRepresentative(g));
  }
}

void EagerInstantiation::processNewTerms()
{
  if (d_qstate.isInConflict() || !d_qstate.getEqualityEngine()->consistent())
  {
    return;
  }
  CodeTimer codeTimer(d_procTime);
  d_round++;
  int64_t prevPairs = d_statPairs.get();
  int64_t prevMatches = d_statMatches.get();
  int64_t prevInst = d_statInst.get();
  uint64_t instLimit = options().quantifiers.eagerInstLimit;
  uint64_t pairLimit = options().quantifiers.eagerInstPairLimit;
  if (options().quantifiers.eagerInstMerge
      || options().quantifiers.eagerInstRlv)
  {
    processMerges();
  }
  bool finished = false;
  for (std::pair<const Node, std::vector<std::unique_ptr<EagerTrigger>>>& ot :
       d_opTriggers)
  {
    std::map<Node, std::unique_ptr<OpTermList>>::iterator itt =
        d_opTerms.find(ot.first);
    if (itt == d_opTerms.end())
    {
      continue;
    }
    promoteTerms(*itt->second);
    context::CDList<Node>& terms = itt->second->d_unique;
    context::CDList<Node>& sigs = itt->second->d_uniqueSigs;
    size_t nterms = terms.size();
    // Group the triggers that have terms to process by their cursor, so
    // that we can iterate the term list once per group and look up the
    // candidate triggers per term via the representative of their indexed
    // ground argument. This avoids enumerating all (term, trigger)
    // combinations for operators with many triggers that differ in a
    // ground argument (e.g. has_type patterns). Cursors within a group
    // are usually identical, since triggers of the same operator advance
    // in lockstep unless they are activated at different times or
    // processing was interrupted.
    std::map<size_t, std::vector<EagerTrigger*>> groups;
    for (std::unique_ptr<EagerTrigger>& tr : ot.second)
    {
      size_t i = tr->d_procIdx.get();
      if (i >= nterms || !d_activeQuants.contains(tr->d_quant))
      {
        // up to date, or the quantified formula is not (yet) asserted; in
        // the latter case we do not advance the cursor, so that we match
        // against all existing terms if it is asserted later
        continue;
      }
      refreshTriggerCache(*tr);
      if (!tr->d_roundActive)
      {
        // the pattern cannot match this round; do not advance the cursor
        continue;
      }
      groups[i].push_back(tr.get());
    }
    for (std::pair<const size_t, std::vector<EagerTrigger*>>& g : groups)
    {
      // Build the ground-argument index for this group: a trigger with at
      // least one ground argument is indexed by the representative of its
      // first one; the remaining triggers must be considered for every
      // term.
      std::vector<EagerTrigger*> unconstrained;
      std::map<size_t, std::unordered_map<Node, std::vector<EagerTrigger*>>>
          posIndex;
      for (EagerTrigger* tr : g.second)
      {
        if (tr->d_groundPos.empty())
        {
          unconstrained.push_back(tr);
        }
        else
        {
          posIndex[tr->d_groundPos[0]][tr->d_groundReps[0]].push_back(tr);
        }
      }
      Trace("eager-inst-debug")
          << "Eager inst: process terms [" << g.first << ", " << nterms
          << ") of " << ot.first << " for " << g.second.size() << " triggers"
          << std::endl;
      size_t i = g.first;
      std::vector<EagerTrigger*> candidates;
      while (i < nterms && !finished)
      {
        TNode t = terms[i];
        TNode sig = sigs[i];
        i++;
        candidates.clear();
        candidates.insert(
            candidates.end(), unconstrained.begin(), unconstrained.end());
        for (std::pair<const size_t,
                       std::unordered_map<Node, std::vector<EagerTrigger*>>>&
                 pi : posIndex)
        {
          // the triggers whose indexed ground argument has the same
          // representative as the corresponding argument of this term
          std::unordered_map<Node, std::vector<EagerTrigger*>>::iterator itpi =
              pi.second.find(sig[pi.first]);
          if (itpi != pi.second.end())
          {
            candidates.insert(
                candidates.end(), itpi->second.begin(), itpi->second.end());
          }
        }
        for (EagerTrigger* tr : candidates)
        {
          resourceManager()->spendResource(Resource::QuantifierStep);
          ++d_statPairs;
          processTermForTrigger(t, sig, *tr);
          if (d_qstate.isInConflict())
          {
            // stop processing, but remember how far we got
            finished = true;
            break;
          }
          if (instLimit > 0
              && d_statInst.get() - prevInst >= static_cast<int64_t>(instLimit))
          {
            // met the limit of instantiations for this round
            finished = true;
            break;
          }
          if (pairLimit > 0
              && d_statPairs.get() - prevPairs
                     >= static_cast<int64_t>(pairLimit))
          {
            // met the limit of considered pairs for this round
            finished = true;
            break;
          }
        }
      }
      // Note that if we were interrupted while processing the candidate
      // triggers of a term, the remaining candidates skip that term; such
      // misses are found by the lazy instantiation engine.
      for (EagerTrigger* tr : g.second)
      {
        tr->d_procIdx = i;
      }
      if (finished)
      {
        break;
      }
    }
    if (finished)
    {
      break;
    }
  }
  if (TraceIsOn("eager-inst-status"))
  {
    int64_t p = d_statPairs.get() - prevPairs;
    if (p > 0)
    {
      Trace("eager-inst-status")
          << "Eager inst: round processed " << p << " pairs, found "
          << (d_statMatches.get() - prevMatches) << " matches, added "
          << (d_statInst.get() - prevInst) << " instantiations"
          << (d_qstate.isInConflict() ? " (conflict)" : "") << std::endl;
    }
  }
}

void EagerInstantiation::processTermForTrigger(TNode t,
                                               TNode sig,
                                               const EagerTrigger& tr)
{
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  Assert(ee->hasTerm(t));
  const Node& q = tr.d_quant;
  const Node& pat = tr.d_pattern;
  Assert(pat.getNumChildren() == t.getNumChildren());
  size_t nchild = pat.getNumChildren();
  // Cheap top-level filter before doing any allocation: ground arguments of
  // the pattern must be equal to the corresponding argument of t. This
  // rejects the vast majority of pairs for operators with many triggers
  // that differ in a ground argument (e.g. has_type patterns). When the
  // signature of t is available and was computed this round, this amounts
  // to pointer comparisons against the cached representatives of the
  // ground arguments of the pattern. A stale signature (computed at an
  // earlier round, which can occur when a trigger is catching up after
  // late activation) may spuriously reject; such misses are found by the
  // lazy instantiation engine.
  if (!tr.d_groundPos.empty())
  {
    Assert(tr.d_roundStamp == d_round && tr.d_roundActive);
    if (!sig.isNull())
    {
      for (size_t k = 0, ngp = tr.d_groundPos.size(); k < ngp; k++)
      {
        if (sig[tr.d_groundPos[k]] != tr.d_groundReps[k])
        {
          return;
        }
      }
    }
    else
    {
      for (size_t k = 0, ngp = tr.d_groundPos.size(); k < ngp; k++)
      {
        TNode pc = pat[tr.d_groundPos[k]];
        if (!ee->hasTerm(pc) || !ee->areEqual(pc, t[tr.d_groundPos[k]]))
        {
          return;
        }
      }
    }
  }
  // match the arguments of the pattern against the arguments of t
  std::vector<std::pair<TNode, TNode>> todo;
  for (size_t i = 0; i < nchild; i++)
  {
    todo.emplace_back(pat[i], t[i]);
  }
  std::map<Node, Node> binding;
  std::vector<std::map<Node, Node>> matches;
  matchRec(0, todo, binding, matches);
  if (!tr.d_otherPatterns.empty() && !matches.empty())
  {
    // for a multi-trigger, extend the matches of the focus pattern to the
    // remaining patterns, matching against existing terms
    std::vector<std::map<Node, Node>> fullMatches;
    for (std::map<Node, Node>& m : matches)
    {
      matchMultiRec(tr, 0, m, fullMatches);
    }
    matches = std::move(fullMatches);
  }
  // We skip instantiations whose fingerprint (the quantified formula and
  // the tuple of representatives of the terms) we have already sent, so
  // that we send at most one instantiation per equivalence-class tuple.
  std::vector<Node> instFp;
  Instantiate* ie = d_qim.getInstantiate();
  for (const std::map<Node, Node>& m : matches)
  {
    std::vector<Node> terms;
    instFp.clear();
    instFp.push_back(q);
    bool success = true;
    for (const Node& v : q[0])
    {
      std::map<Node, Node>::const_iterator itm = m.find(v);
      if (itm == m.end())
      {
        // should not happen by trigger registration, but be safe
        success = false;
        break;
      }
      terms.push_back(itm->second);
      instFp.push_back(ee->getRepresentative(itm->second));
    }
    if (!success)
    {
      continue;
    }
    Node fp = nodeManager()->mkNode(Kind::SEXPR, instFp);
    if (d_sentFps.contains(fp))
    {
      // duplicate modulo equality of an instantiation we already sent
      continue;
    }
    d_sentFps.insert(fp);
    Trace("eager-inst-debug") << "Eager inst: match " << q << " with " << terms
                              << " from term " << t << std::endl;
    ++d_statMatches;
    // We disable the entailment check, since it relies on state of TermDb
    // that is only valid during full effort instantiation rounds.
    bool addSuccess;
    {
      CodeTimer instTimer(d_addInstTime);
      addSuccess =
          ie->addInstantiation(q,
                               terms,
                               InferenceId::QUANTIFIERS_INST_E_MATCHING_EAGER,
                               Node::null(),
                               false,
                               false);
    }
    if (addSuccess)
    {
      ++d_statInst;
      Trace("eager-inst") << "Eager inst: success " << q << " with " << terms
                          << std::endl;
      if (options().quantifiers.eagerInstGenLimit > 0)
      {
        // Compute the generation of this instantiation, which is one more
        // than the maximal generation of the instantiating terms, and
        // assign it to the (new) APPLY_UF subterms of the instance body.
        uint64_t g = 0;
        for (const Node& tt : terms)
        {
          std::unordered_map<Node, uint64_t>::iterator itg = d_termGen.find(tt);
          if (itg != d_termGen.end() && itg->second > g)
          {
            g = itg->second;
          }
        }
        g++;
        std::vector<Node> vars(q[0].begin(), q[0].end());
        Node body = q[1].substitute(
            vars.begin(), vars.end(), terms.begin(), terms.end());
        std::unordered_set<Node> bts;
        expr::getSubtermsKind(Kind::APPLY_UF, body, bts);
        for (const Node& s : bts)
        {
          // keep the smaller generation if already assigned
          if (d_termGen.find(s) == d_termGen.end())
          {
            d_termGen[s] = g;
          }
        }
      }
    }
    if (d_qstate.isInConflict())
    {
      return;
    }
  }
}

void EagerInstantiation::matchMultiRec(
    const EagerTrigger& tr,
    size_t patIdx,
    std::map<Node, Node>& binding,
    std::vector<std::map<Node, Node>>& matches)
{
  // A hard cap on the matches considered per focus pair, to bound the
  // cross-product enumeration of multi-trigger matching. Matches beyond
  // this limit are found by the lazy instantiation engine.
  constexpr size_t multiMatchLimit = 1000;
  if (patIdx == tr.d_otherPatterns.size())
  {
    matches.push_back(binding);
    return;
  }
  const Node& p = tr.d_otherPatterns[patIdx];
  Node op = p.getOperator();
  std::map<Node, std::unique_ptr<OpTermList>>::iterator itt =
      d_opTerms.find(op);
  if (itt == d_opTerms.end())
  {
    return;
  }
  context::CDList<Node>& terms = itt->second->d_unique;
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  size_t nterms = terms.size();
  std::vector<std::pair<TNode, TNode>> todo;
  for (size_t i = 0; i < nterms; i++)
  {
    if (matches.size() >= multiMatchLimit)
    {
      return;
    }
    TNode u = terms[i];
    if (!ee->hasTerm(u))
    {
      continue;
    }
    ++d_statPairs;
    Assert(u.getNumChildren() == p.getNumChildren());
    todo.clear();
    for (size_t j = 0, nchild = p.getNumChildren(); j < nchild; j++)
    {
      todo.emplace_back(p[j], u[j]);
    }
    std::vector<std::map<Node, Node>> sub;
    matchRec(0, todo, binding, sub);
    for (std::map<Node, Node>& sm : sub)
    {
      matchMultiRec(tr, patIdx + 1, sm, matches);
    }
  }
}

void EagerInstantiation::matchRec(size_t i,
                                  std::vector<std::pair<TNode, TNode>>& todo,
                                  std::map<Node, Node>& binding,
                                  std::vector<std::map<Node, Node>>& matches)
{
  if (i == todo.size())
  {
    matches.push_back(binding);
    return;
  }
  TNode p = todo[i].first;
  TNode t = todo[i].second;
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  if (p.getKind() == Kind::BOUND_VARIABLE)
  {
    std::map<Node, Node>::iterator itb = binding.find(p);
    if (itb != binding.end())
    {
      // non-linear occurrence, the binding must be equal to t
      if (itb->second == t || ee->areEqual(itb->second, t))
      {
        matchRec(i + 1, todo, binding, matches);
      }
      return;
    }
    binding[p] = t;
    matchRec(i + 1, todo, binding, matches);
    binding.erase(p);
    return;
  }
  if (!expr::hasBoundVar(p))
  {
    // ground subterm, must be equal to t in the current context
    if (ee->hasTerm(p) && ee->areEqual(p, t))
    {
      matchRec(i + 1, todo, binding, matches);
    }
    return;
  }
  if (p.getKind() != Kind::APPLY_UF)
  {
    // unhandled pattern shape (e.g. interpreted symbols over bound
    // variables), this trigger is handled by the lazy engine only
    return;
  }
  // find a term in the equivalence class of t whose operator matches
  Node op = p.getOperator();
  Node r = ee->getRepresentative(t);
  size_t base = todo.size();
  // We consider only one candidate per tuple of argument representatives,
  // since congruent candidates yield the same matches modulo equality.
  std::set<std::vector<TNode>> seenSigs;
  std::vector<TNode> sig;
  eq::EqClassIterator eqc(r, ee);
  while (!eqc.isFinished())
  {
    TNode s = *eqc;
    ++eqc;
    if (s.getKind() != Kind::APPLY_UF || s.getOperator() != op)
    {
      continue;
    }
    Assert(s.getNumChildren() == p.getNumChildren());
    sig.clear();
    for (const TNode& sc : s)
    {
      sig.push_back(ee->getRepresentative(sc));
    }
    if (!seenSigs.insert(sig).second)
    {
      // congruent to a candidate we already tried
      continue;
    }
    for (size_t j = 0, nchild = p.getNumChildren(); j < nchild; j++)
    {
      todo.emplace_back(p[j], s[j]);
    }
    matchRec(i + 1, todo, binding, matches);
    todo.resize(base);
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
