/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Quantifier reasoning for the eager E-matching core.
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

#include "theory/quantifiers/eager/quantifier_manager.h"

#include <algorithm>

#include "base/output.h"
#include "options/quantifiers_options.h"
#include "smt/env.h"
#include "theory/quantifiers/eager/enode.h"
#include "theory/quantifiers/eager/mam.h"
#include "theory/quantifiers/eager/quantifier_normalizer.h"
#include "theory/quantifiers/eager/smt_context.h"
#include "theory/quantifiers/eager/statistics.h"
#include "theory/quantifiers/eager/trail.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

QuantifierManager::QuantifierManager(Env& env, SmtContext& ctx)
    : EnvObj(env),
      d_context(ctx),
      d_queue(env, *this, ctx),
      d_fingerprints(ctx.getTrailStack()),
      d_active(false)
{
  d_queue.setup();
  d_mam = std::make_unique<Mam>(ctx, *this);
}

QuantifierManager::~QuantifierManager() {}

void QuantifierManager::add(TNode q, uint32_t generation)
{
  d_generations[q] = generation;
  d_quantifiers.push_back(q);
}

void QuantifierManager::del(TNode q)
{
  d_quantifiers.pop_back();
  d_generations.erase(q);
}

uint32_t QuantifierManager::getGeneration(TNode q) const
{
  auto it = d_generations.find(q);
  return it == d_generations.end() ? 0 : it->second;
}

bool QuantifierManager::addInstance(TNode q,
                                    size_t numBindings,
                                    ENode* const* bindings,
                                    uint32_t maxGeneration)
{
  if (d_generations.count(q) == 0)
  {
    return false;
  }
  maxGeneration = std::max(maxGeneration, getGeneration(q));
  Fingerprint* f = d_fingerprints.insert(q, numBindings, bindings);
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

void QuantifierManager::initSearch() { d_queue.initSearch(); }

void QuantifierManager::notifyAssigned(TNode q)
{
  d_active = true;
  if (q.getNumChildren() != 3)
  {
    return;
  }
  // every pattern, including the multi-patterns, is matched eagerly
  for (const Node& mp : q[2])
  {
    if (mp.getKind() == Kind::INST_PATTERN)
    {
      d_mam->addPattern(q, mp);
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
    d_mam->notifyRelevant(n);
  }
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

void QuantifierManager::notifyPop()
{
  d_mam->notifyPop();
  d_queue.notifyPop();
}

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal
