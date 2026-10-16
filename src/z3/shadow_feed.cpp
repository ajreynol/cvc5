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

#include "z3/shadow_feed.h"

#include <algorithm>

#include "expr/node_algorithm.h"
#include "options/z3_options.h"
#include "theory/uf/equality_engine.h"
#include "z3/shared_backend.h"
#include "z3/smt_context.h"

namespace cvc5::internal {
namespace z3 {

ShadowFeed::ShadowFeed(Env& env, SharedBackend& backend)
    : EnvObj(env),
      d_backend(backend),
      d_master(nullptr),
      d_import(options().z3.z3ShadowImport),
      d_coreTerm(context()),
      d_coreIdx(context(), 0)
{
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

void ShadowFeed::eqNotifyNewClass(TNode /*t*/) {}

void ShadowFeed::eqNotifyMerge(TNode t1, TNode t2)
{
  // The Boolean classes are those of the atoms, whose values reach the core
  // as facts.
  if (!t1.getType().isBoolean())
  {
    d_pending.emplace_back(t1, t2);
  }
}

void ShadowFeed::eqNotifyDisequal(TNode /*t1*/,
                                  TNode /*t2*/,
                                  TNode /*reason*/)
{
}

Node ShadowFeed::coreTermOf(TNode rep) const
{
  auto it = d_coreTerm.find(rep);
  return it == d_coreTerm.end() ? Node::null() : it->second;
}

void ShadowFeed::merge(TNode a, TNode b)
{
  SmtContext& ctx = d_backend.getContext();
  if (a == b || !ctx.eInternalized(a) || !ctx.eInternalized(b))
  {
    return;
  }
  ctx.assumeExternalEq(a, b);
  ctx.getStats().d_numShadowMerges++;
}

bool ShadowFeed::import(TNode t, TNode other)
{
  SmtContext& ctx = d_backend.getContext();
  if (ctx.eInternalized(t))
  {
    return true;
  }
  if (expr::hasBoundVar(t) || expr::hasClosure(t))
  {
    return false;
  }
  ENode* o = ctx.getENode(other);
  ctx.internalize(t, false, ctx.getGeneration(o));
  if (!ctx.eInternalized(t))
  {
    return false;
  }
  // as Z3's datatype plugin does with the terms it makes
  ctx.markAsRelevant(ctx.getENode(t));
  ctx.getStats().d_numShadowImports++;
  return true;
}

void ShadowFeed::apply()
{
  if (d_master == nullptr)
  {
    return;
  }
  SmtContext& ctx = d_backend.getContext();
  if (ctx.inconsistent())
  {
    d_pending.clear();
    return;
  }
  // The merges notified, in order: each is keyed by the representatives of
  // the time, as d_coreTerm is.
  for (const std::pair<Node, Node>& p : d_pending)
  {
    const Node& r1 = p.first;
    const Node& r2 = p.second;
    Node c1 = coreTermOf(r1);
    Node c2 = coreTermOf(r2);
    if (c1.isNull() && c2.isNull())
    {
      continue;
    }
    if (c1.isNull())
    {
      // r1 represents the merged class, which now holds c2
      if (d_import && import(r1, c2))
      {
        merge(r1, c2);
      }
      d_coreTerm.insert(r1, c2);
      continue;
    }
    if (c2.isNull())
    {
      if (d_import && import(r2, c1))
      {
        merge(r2, c1);
      }
      continue;
    }
    merge(c1, c2);
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
      if (r != t && d_import && import(r, t))
      {
        merge(r, t);
      }
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
