/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Quantifier reasoning for the ported Z3 core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_quantifier.cpp, and recast in cvc5 style.
 *
 * Not ported: higher-order matching, and the model finder and model checker
 * that implement model based quantifier instantiation. Without the latter,
 * checkModel always answers "unknown", so a quantified problem whose search
 * ends in a satisfying assignment is reported as unknown rather than sat --
 * which is what Z3 itself does when it gives up on the quantifiers.
 */

#include "z3/quantifiers/quantifier_manager.h"

#include <algorithm>

#include "base/output.h"
#include "options/z3_options.h"
#include "smt/env.h"
#include "z3/quantifiers/enode.h"
#include "z3/quantifiers/mam.h"
#include "z3/quantifiers/smt_context.h"
#include "z3/util/ast.h"
#include "z3/util/statistics.h"
#include "z3/util/trail.h"

namespace cvc5::internal {
namespace z3 {

namespace {

/**
 * How many times the final check rematches the multi-patterns that are not
 * matched eagerly (Z3's qi.max_lazy_multipattern_matching).
 */
constexpr size_t s_maxLazyMultipatternMatching = 2;

}  // namespace

QuantifierManager::QuantifierManager(SmtContext& ctx)
    : d_context(ctx),
      d_queue(*this, ctx),
      d_fingerprints(ctx.getTrailStack()),
      d_qstatGen(ctx.getTrailStack()),
      d_lazyMatchingIdx(0),
      d_active(false),
      d_lazyScopes(0),
      d_lazy(true)
{
  d_queue.setup();
  d_mam = mkMam(ctx, *this);
  d_lazyMam = mkMam(ctx, *this);
}

QuantifierManager::~QuantifierManager() {}

void QuantifierManager::add(TNode q, uint32_t generation)
{
  if (d_lazy)
  {
    while (d_lazyScopes > 0)
    {
      --d_lazyScopes;
      pushCore();
    }
    d_lazy = false;
  }
  QuantifierStat* stat = d_qstatGen(q, generation);
  d_quantifierStat[q] = stat;
  d_id2Quant[q.getId()] = q;
  d_quantifiers.push_back(q);
}

void QuantifierManager::del(TNode q)
{
  d_quantifiers.pop_back();
  d_quantifierStat.erase(q);
}

QuantifierStat* QuantifierManager::getStat(TNode q) const
{
  auto it = d_quantifierStat.find(q);
  Assert(it != d_quantifierStat.end());
  return it->second;
}

TNode QuantifierManager::getQuantifierById(uint64_t id) const
{
  auto it = d_id2Quant.find(id);
  Assert(it != d_id2Quant.end());
  return it->second;
}

uint32_t QuantifierManager::getGeneration(TNode q) const
{
  auto it = d_quantifierStat.find(q);
  return it == d_quantifierStat.end() ? 0 : it->second->getGeneration();
}

bool QuantifierManager::addInstance(TNode q,
                                    size_t numBindings,
                                    ENode* const* bindings,
                                    uint32_t maxGeneration)
{
  if (d_quantifierStat.count(q) == 0)
  {
    return false;
  }
  maxGeneration = std::max(maxGeneration, getGeneration(q));
  getStat(q)->updateMaxGeneration(maxGeneration);
  Fingerprint* f = d_fingerprints.insert(
      q.getId(), static_cast<uint32_t>(q.getId()), numBindings, bindings);
  if (f != nullptr)
  {
    d_queue.insert(f, maxGeneration);
  }
  else
  {
    d_context.getStats().d_numMissedInstances++;
  }
  return f != nullptr;
}

void QuantifierManager::initSearch()
{
  for (const Node& q : d_quantifiers)
  {
    getStat(q)->resetNumInstancesCurrSearch();
  }
  d_queue.initSearch();
  d_lazyMatchingIdx = 0;
}

void QuantifierManager::notifyAssigned(TNode q)
{
  d_active = true;
  // A multi-pattern is only matched eagerly up to a bound, since matching
  // one is much more expensive than matching a unary pattern. The bound is
  // raised by one when the quantifier has no unary pattern at all, so that
  // at least one of its patterns is always matched eagerly.
  std::vector<std::vector<Node>> patterns;
  getPatterns(q, patterns);
  bool hasUnaryPattern = false;
  for (const std::vector<Node>& mp : patterns)
  {
    if (mp.size() == 1)
    {
      hasUnaryPattern = true;
      break;
    }
  }
  uint32_t numEagerMultiPatterns = static_cast<uint32_t>(
      d_context.getEnv().getOptions().z3.z3QiMaxMultiPatterns);
  if (!hasUnaryPattern)
  {
    numEagerMultiPatterns++;
  }
  if (q.getNumChildren() != 3)
  {
    return;
  }
  size_t j = 0;
  for (const Node& mp : q[2])
  {
    if (mp.getKind() != Kind::INST_PATTERN)
    {
      continue;
    }
    bool unary = mp.getNumChildren() == 1;
    if (!unary && j >= numEagerMultiPatterns)
    {
      d_lazyMam->addPattern(q, mp);
    }
    else
    {
      d_mam->addPattern(q, mp);
    }
    if (!unary)
    {
      j++;
    }
  }
}

void QuantifierManager::notifyMerge(ENode* n1, ENode* n2)
{
  if (!empty())
  {
    d_mam->notifyMerge(n1, n2);
  }
}

void QuantifierManager::notifyRelevant(ENode* n)
{
  if (!empty())
  {
    d_mam->notifyRelevant(n, false);
    d_lazyMam->notifyRelevant(n, true);
  }
}

FinalCheckStatus QuantifierManager::finalCheck(bool full)
{
  if (!full)
  {
    return FC_DONE;
  }
  FinalCheckStatus result = d_queue.finalCheck() ? FC_DONE : FC_CONTINUE;
  if (!empty() && d_lazyMatchingIdx < s_maxLazyMultipatternMatching)
  {
    d_lazyMam->rematch();
    d_context.pushTrail(ValueTrail<size_t>(d_lazyMatchingIdx));
    d_lazyMatchingIdx++;
  }
  if (d_context.canPropagate())
  {
    result = FC_CONTINUE;
  }
  return result;
}

bool QuantifierManager::canPropagate() const
{
  return d_queue.hasWork() || (d_active && d_mam->hasWork());
}

void QuantifierManager::propagate()
{
  if (d_active)
  {
    d_mam->match();
  }
  d_queue.instantiate();
}

void QuantifierManager::pushCore()
{
  d_mam->pushScope();
  d_lazyMam->pushScope();
  d_queue.pushScope();
}

void QuantifierManager::push()
{
  if (d_lazy)
  {
    ++d_lazyScopes;
  }
  else
  {
    pushCore();
  }
  d_fingerprints.pushScope();
}

void QuantifierManager::pop(size_t numScopes)
{
  if (d_lazy)
  {
    d_lazyScopes -= numScopes;
  }
  else
  {
    d_mam->popScope(numScopes);
    d_lazyMam->popScope(numScopes);
    d_queue.popScope(numScopes);
  }
  d_fingerprints.popScope(numScopes);
}

}  // namespace z3
}  // namespace cvc5::internal
