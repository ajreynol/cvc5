/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The equalities of cvc5's theories, for the shadow of the ported core.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "z3/quantifiers/shadow_feed.h"

#include <algorithm>
#include <map>

#include "options/z3_options.h"
#include "theory/uf/equality_engine.h"
#include "z3/quantifiers/enode.h"
#include "z3/quantifiers/host_core.h"
#include "z3/quantifiers/smt_context.h"

namespace cvc5::internal {
namespace z3 {

ShadowFeed::ShadowFeed(Env& env, HostCore& core)
    : EnvObj(env),
      d_core(core),
      d_master(nullptr),
      d_coreTerm(context()),
      d_coreIdx(context(), 0),
      d_replay(options().z3.z3Mirror == options::Z3MirrorMode::EQUALITIES)
{
}

void ShadowFeed::notifyPop(uint32_t lvl)
{
  auto above = [lvl](const auto& p) { return p.d_lvl > lvl; };
  if (!d_replay)
  {
    d_pending.clear();
    return;
  }
  d_pending.erase(std::remove_if(d_pending.begin(), d_pending.end(), above),
                  d_pending.end());
  d_reapply.erase(std::remove_if(d_reapply.begin(), d_reapply.end(), above),
                  d_reapply.end());
  // the changes applied above lvl, which the core undoes; d_reapply keeps
  // the order in which they were applied
  size_t k = d_applied.size();
  while (k > 0 && d_applied[k - 1].d_appliedLvl > lvl)
  {
    --k;
  }
  std::vector<Applied> undone;
  for (size_t i = k, n = d_applied.size(); i < n; ++i)
  {
    if (d_applied[i].d_lvl <= lvl)
    {
      undone.push_back(d_applied[i]);
    }
  }
  d_applied.resize(k);
  d_reapply.insert(d_reapply.begin(), undone.begin(), undone.end());
}

ShadowFeed::~ShadowFeed() {}

bool ShadowFeed::eqNotifyTriggerPredicate(TNode /*predicate*/, bool /*value*/)
{
  return true;
}

bool ShadowFeed::eqNotifyTriggerTermEquality(theory::TheoryId /*tag*/,
                                             TNode /*t1*/,
                                             TNode /*t2*/,
                                             bool /*value*/)
{
  return true;
}

void ShadowFeed::eqNotifyConstantTermMerge(TNode /*t1*/, TNode /*t2*/) {}

void ShadowFeed::eqNotifyNewClass(TNode t)
{
  // A term the core internalized before cvc5 registered it was not found in
  // the master equality engine when looked up (see apply), so it is
  // recorded now, for the merges of its class.
  if (d_replay && !t.getType().isBoolean()
      && d_core.getContext().eInternalized(t))
  {
    d_coreTerm.insert(t, t);
  }
}

void ShadowFeed::eqNotifyMerge(TNode t1, TNode t2)
{
  // The Boolean classes are those of the atoms, whose values reach the core
  // as facts.
  if (!t1.getType().isBoolean())
  {
    d_pending.push_back({t1, t2, context()->getLevel()});
  }
}

void ShadowFeed::eqNotifyDisequal(TNode /*t1*/, TNode /*t2*/, TNode /*reason*/)
{
}

Node ShadowFeed::coreTermOf(TNode rep)
{
  auto it = d_coreTerm.find(rep);
  if (!d_replay)
  {
    return it == d_coreTerm.end() ? Node::null() : it->second;
  }
  // With --z3-mirror=equalities, the record may be stale: the pops of the
  // SAT context undo records the core still holds, and the core may have
  // internalized a term before cvc5 registered it. A term of the core in the
  // class is then looked for in the master equality engine.
  SmtContext& ctx = d_core.getContext();
  if (it != d_coreTerm.end() && ctx.eInternalized(it->second)
      && d_master->hasTerm(it->second)
      && d_master->getRepresentative(it->second) == rep)
  {
    return it->second;
  }
  if (!d_master->hasTerm(rep))
  {
    return Node::null();
  }
  theory::eq::EqClassIterator eqc(rep, d_master);
  for (; !eqc.isFinished(); ++eqc)
  {
    Node t = *eqc;
    if (ctx.eInternalized(t))
    {
      d_coreTerm.insert(rep, t);
      return t;
    }
  }
  return Node::null();
}

void ShadowFeed::merge(TNode a, TNode b)
{
  SmtContext& ctx = d_core.getContext();
  if (a == b || !ctx.eInternalized(a) || !ctx.eInternalized(b)
      || ctx.getENode(a)->getRoot() == ctx.getENode(b)->getRoot())
  {
    return;
  }
  ctx.assumeExternalEq(a, b);
  ctx.getStats().d_numShadowMerges++;
}

void ShadowFeed::applyMerge(TNode rep, TNode c, bool isMap, uint32_t lvl)
{
  if (isMap)
  {
    d_coreTerm.insert(rep, c);
  }
  else
  {
    merge(rep, c);
  }
  if (d_replay)
  {
    d_applied.push_back({rep, c, isMap, lvl, context()->getLevel()});
  }
}

// TEMPORARY diagnostic
void ShadowFeed::debugCheck()
{
  if (d_master == nullptr)
  {
    return;
  }
  if (TraceIsOn("z3-unmerged"))
  {
    debugCheckCore();
  }
}

void ShadowFeed::debugCheckCore()
{
  SmtContext& ctx = d_core.getContext();
  std::map<Node, Node> first;
  for (size_t i = 0, n = ctx.getNumEInternalized(); i < n; ++i)
  {
    TNode t = ctx.getEInternalized(i);
    if (t.getType().isBoolean() || !d_master->hasTerm(t))
    {
      continue;
    }
    Node r = d_master->getRepresentative(t);
    auto it = first.emplace(r, t);
    if (!it.second
        && ctx.getENode(t)->getRoot() != ctx.getENode(it.first->second)->getRoot())
    {
      Node ct = coreTermOf(r);
      Trace("z3-unmerged") << "feed-unmerged idx " << i << "/" << d_coreIdx.get()
                           << " lvl " << context()->getLevel() << " " << t
                           << " == " << it.first->second << " rep " << r
                           << " coreTermOf(rep) " << ct << std::endl;
    }
  }
}

void ShadowFeed::apply()
{
  if (d_master == nullptr)
  {
    return;
  }
  SmtContext& ctx = d_core.getContext();
  if (ctx.inconsistent())
  {
    d_pending.clear();
    return;
  }
  // the changes undone by pops that the master equality engine keeps
  std::vector<Applied> reapply;
  reapply.swap(d_reapply);
  for (const Applied& a : reapply)
  {
    if (ctx.eInternalized(a.d_b) && (a.d_isMap || ctx.eInternalized(a.d_a)))
    {
      applyMerge(a.d_a, a.d_b, a.d_isMap, a.d_lvl);
    }
  }
  // The merges notified, in order: each is keyed by the representatives of
  // the time, as d_coreTerm is.
  for (const Pending& p : d_pending)
  {
    const Node& r1 = p.d_r1;
    const Node& r2 = p.d_r2;
    Node c1 = coreTermOf(r1);
    Node c2 = coreTermOf(r2);
    if (c1.isNull() && c2.isNull())
    {
      continue;
    }
    if (c1.isNull())
    {
      // r1 represents the merged class, which now holds c2
      applyMerge(r1, c2, true, p.d_lvl);
      continue;
    }
    if (c2.isNull())
    {
      continue;
    }
    applyMerge(c1, c2, false, p.d_lvl);
  }
  d_pending.clear();
  // The terms the core internalized since the last call, which may have
  // been merged in the master equality engine before.
  size_t n = ctx.getNumEInternalized();
  for (size_t i = std::min(d_coreIdx.get(), n); i < n; ++i)
  {
    TNode t = ctx.getEInternalized(i);
    if (t.getType().isBoolean() || !d_master->hasTerm(t))
    {
      continue;
    }
    Node r = d_master->getRepresentative(t);
    Node c = coreTermOf(r);
    if (c.isNull())
    {
      d_coreTerm.insert(r, t);
    }
    else
    {
      merge(t, c);
    }
  }
  d_coreIdx = n;
}

}  // namespace z3
}  // namespace cvc5::internal
