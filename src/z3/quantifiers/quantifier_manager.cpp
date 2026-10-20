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
#include <sstream>

#include "base/output.h"
#include "z3/util/ast.h"
#include "z3/quantifiers/enode.h"
#include "z3/quantifiers/mam.h"
#include "z3/quantifiers/smt_context.h"
#include "z3/util/statistics.h"
#include "z3/util/trail.h"

namespace cvc5::internal {
namespace z3 {

QuantifierManager::QuantifierManager(SmtContext& ctx, Params& p)
    : d_context(ctx),
      d_params(p),
      d_queue(*this, ctx, p),
      d_fingerprints(ctx.getRegion()),
      d_qstatGen(ctx.getRegion()),
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
                                    TNode pat,
                                    size_t numBindings,
                                    ENode* const* bindings,
                                    uint32_t maxGeneration,
                                    uint32_t minTopGeneration,
                                    uint32_t maxTopGeneration)
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
    d_queue.insert(f, pat, maxGeneration, minTopGeneration, maxTopGeneration);
  }
  else
  {
    d_context.getStats().d_numMissedInstances++;
  }
  return f != nullptr;
}

void QuantifierManager::initSearchEh()
{
  for (const Node& q : d_quantifiers)
  {
    getStat(q)->resetNumInstancesCurrSearch();
  }
  d_queue.initSearchEh();
  d_lazyMatchingIdx = 0;
}

void QuantifierManager::assignEh(TNode q)
{
  d_active = true;
  if (TraceIsOn("z3-qpat"))
  {
    size_t numPats = 0;
    std::stringstream arities;
    if (q.getNumChildren() == 3)
    {
      for (const Node& a : q[2])
      {
        if (a.getKind() == Kind::INST_PATTERN)
        {
          numPats++;
          arities << " " << a.getNumChildren();
        }
      }
    }
    Trace("z3-qpat") << "[assign-quant] q" << q.getId() << " pats=" << numPats
                     << " arity" << arities.str() << " " << q << std::endl;
  }
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
  uint32_t numEagerMultiPatterns = d_params.d_qiMaxEagerMultipatterns;
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

void QuantifierManager::addEqEh(ENode* n1, ENode* n2)
{
  if (!empty())
  {
    d_mam->addEqEh(n1, n2);
  }
}

void QuantifierManager::relevantEh(ENode* n)
{
  if (!empty())
  {
    d_mam->relevantEh(n, false);
    d_lazyMam->relevantEh(n, true);
  }
}

FinalCheckStatus QuantifierManager::finalCheckEh(bool full)
{
  if (!full)
  {
    return FC_DONE;
  }
  FinalCheckStatus result = d_queue.finalCheckEh() ? FC_DONE : FC_CONTINUE;
  if (!empty() && d_lazyMatchingIdx < d_params.d_qiMaxLazyMultipatternMatching)
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
