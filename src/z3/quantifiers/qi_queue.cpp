/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The queue of quantifier instantiations.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/qi_queue.cpp, and recast in cvc5 style.
 */

#include "z3/quantifiers/qi_queue.h"

#include <algorithm>
#include <unordered_map>

#include "base/output.h"
#include "options/z3_options.h"
#include "smt/env.h"
#include "z3/util/ast.h"
#include "z3/quantifiers/enode.h"
#include "z3/quantifiers/quantifier_manager.h"
#include "z3/quantifiers/smt_context.h"
#include "z3/quantifiers/quantifier_stat.h"
#include "z3/util/statistics.h"

namespace cvc5::internal {
namespace z3 {

QiQueue::QiQueue(QuantifierManager& qm, SmtContext& ctx)
    : d_qm(qm), d_context(ctx), d_checker(ctx), d_eagerCostThreshold(0)
{
}

void QiQueue::setup()
{
  d_eagerCostThreshold = d_context.getEnv().getOptions().z3.z3QiEagerThreshold;
}

float QiQueue::getCost(TNode q, uint32_t generation)
{
  // Z3's default cost function, qi.cost = (+ weight generation), weight 1
  float r = 1.0f + static_cast<float>(generation);
  d_qm.getStat(q)->updateMaxCost(r);
  return r;
}

void QiQueue::insert(Fingerprint* f, uint32_t generation)
{
  TNode q = getQuantifier(f);
  float cost = getCost(q, generation);
  d_newEntries.push_back(Entry(f, cost, generation));
}

void QiQueue::instantiate()
{
  size_t sinceLastCheck = 0;
  for (Entry& curr : d_newEntries)
  {
    if (d_context.getCancelFlag())
    {
      break;
    }
    if (d_stats.d_numInstances > d_context.getEnv().getOptions().z3.z3QiMaxInstances)
    {
      // the maximum number of quantifier instances was reached
      break;
    }
    Fingerprint* f = curr.d_qb;
    TNode qa = getQuantifier(f);

    if (curr.d_cost <= d_eagerCostThreshold)
    {
      instantiate(curr);
    }
    else if (d_checker.isUnsat(
                 getQuantBody(qa), f->getNumArgs(), f->getArgs()))
    {
      // do not delay an instance that produces a conflict
      instantiate(curr);
    }
    else
    {
      d_delayedEntries.push_back(curr);
    }

    // periodically check that we did not run out of time or memory
    if (sinceLastCheck++ > 100)
    {
      if (d_context.resourceLimitsExceeded())
      {
        break;
      }
      sinceLastCheck = 0;
    }
  }
  d_newEntries.clear();
}

void QiQueue::instantiate(Entry& ent)
{
  if (d_context.inconsistent())
  {
    return;
  }

  Fingerprint* f = ent.d_qb;
  TNode q = getQuantifier(f);
  uint32_t generation = ent.d_generation;
  size_t numBindings = f->getNumArgs();
  ENode* const* bindings = f->getArgs();

  ent.d_instantiated = true;

  QuantifierStat* stat = d_qm.getStat(q);
  if (skipSatisfied(q, stat, numBindings, bindings))
  {
    return;
  }
  std::vector<Node> key{q};
  for (size_t i = 0; i < numBindings; ++i)
  {
    key.push_back(bindings[i]->getExpr());
  }
  Node lemma;
  auto it = d_lemmas.emplace(q.getNodeManager()->mkNode(Kind::SEXPR, key), Node());
  if (it.second)
  {
    lemma = mkLemma(q, stat, numBindings, bindings);
    it.first->second = lemma;
  }
  else
  {
    // made before: counted as mkLemma counts it
    lemma = it.first->second;
    if (lemma.isNull())
    {
      stat->incNumInstancesSimplifyTrue();
      d_context.getStats().d_numInstancesSimplifyTrue++;
    }
    else
    {
      stat->incNumInstances();
      d_context.getStats().d_numInstances++;
    }
  }
  if (lemma.isNull())
  {
    return;
  }
  d_instances.push_back(lemma);
  d_stats.d_numInstances++;
  uint32_t gen = static_cast<uint32_t>(ent.d_cost);
  Trace("z3-qi") << "[instance] q" << q.getId() << " nargs " << numBindings
                 << " gen " << generation << " cost " << ent.d_cost
                 << " newgen " << gen << std::endl;
  Trace("z3-qi-lemma") << "  lemma: " << lemma << std::endl;
  std::vector<Node> terms(key.begin() + 1, key.end());
  d_context.internalizeInstance(q, terms, gen);
}

void QiQueue::pushScope()
{
  Assert(d_context.inconsistent() || d_newEntries.empty());
  d_scopes.push_back(Scope{
      d_delayedEntries.size(), d_instances.size(), d_instantiatedTrail.size()});
}

void QiQueue::popScope(size_t numScopes)
{
  size_t newLvl = d_scopes.size() - numScopes;
  Scope& s = d_scopes[newLvl];
  size_t oldSz = s.d_instantiatedTrailLim;
  size_t sz = d_instantiatedTrail.size();
  for (size_t i = oldSz; i < sz; ++i)
  {
    d_delayedEntries[d_instantiatedTrail[i]].d_instantiated = false;
  }
  d_instantiatedTrail.resize(oldSz);
  d_delayedEntries.erase(d_delayedEntries.begin() + s.d_delayedEntriesLim,
                         d_delayedEntries.end());
  d_instances.resize(s.d_instancesLim);
  d_newEntries.clear();
  d_scopes.resize(newLvl);
}

void QiQueue::initSearchEh() { d_newEntries.clear(); }

bool QiQueue::finalCheckEh()
{
  bool result = true;
  for (size_t i = 0; i < d_delayedEntries.size(); ++i)
  {
    Entry& e = d_delayedEntries[i];
    if (!e.d_instantiated && e.d_cost <= d_context.getEnv().getOptions().z3.z3QiLazyThreshold)
    {
      result = false;
      d_instantiatedTrail.push_back(i);
      d_stats.d_numLazyInstances++;
      d_context.getStats().d_numLazyInstances++;
      instantiate(e);
    }
  }
  return result;
}

namespace {

struct DelayedQaInfo
{
  size_t d_num = 0;
  float d_minCost = 0.0f;
  float d_maxCost = 0.0f;
};

}  // namespace

TNode QiQueue::getQuantifier(Fingerprint* f) const
{
  return d_qm.getQuantifierById(f->getData());
}

bool QiQueue::skipSatisfied(TNode q,
                            QuantifierStat* stat,
                            size_t numBindings,
                            ENode* const* bindings)
{
  if (d_context.getEnv().getOptions().z3.z3QiChecker
      && d_checker.isSat(getQuantBody(q), numBindings, bindings))
  {
    // The instance is already satisfied, so creating it would be wasted
    // work. It still counts as an instantiation, as it does in Z3.
    stat->incNumInstancesCheckerSat();
    d_context.getStats().d_numInstancesCheckerSat++;
    return true;
  }
  return false;
}

Node QiQueue::mkLemma(TNode q,
                      QuantifierStat* stat,
                      size_t numBindings,
                      ENode* const* bindings)
{
  // Substitute the bindings for the canonical quantified variables. Note
  // bindings[i] is the binding of the i-th variable of the bound variable
  // list, which is the variable at de Bruijn level i.
  TNode bvl = q[0];
  Assert(bvl.getNumChildren() == numBindings);
  std::vector<Node> vars;
  std::vector<Node> subs;
  for (size_t i = 0; i < numBindings; ++i)
  {
    vars.push_back(bvl[i]);
    subs.push_back(bindings[i]->getExpr());
  }
  Node instance = getQuantBody(q).substitute(
      vars.begin(), vars.end(), subs.begin(), subs.end());

  Trace("z3-qi-raw") << "RAWINST " << instance << std::endl;
  Trace("z3-events") << "INSTANCE " << instance << std::endl;
  Node sInstance = d_context.rewriteInstance(instance);

  if (sInstance.getKind() == Kind::CONST_BOOLEAN && sInstance.getConst<bool>())
  {
    stat->incNumInstancesSimplifyTrue();
    d_context.getStats().d_numInstancesSimplifyTrue++;
    return Node::null();
  }

  NodeManager* nm = q.getNodeManager();
  Node notQ = nm->mkNode(Kind::NOT, q);
  Node lemma;
  if (sInstance.getKind() == Kind::OR)
  {
    std::vector<Node> args;
    args.push_back(notQ);
    args.insert(args.end(), sInstance.begin(), sInstance.end());
    lemma = nm->mkNode(Kind::OR, args);
  }
  else if (sInstance.getKind() == Kind::CONST_BOOLEAN
           && !sInstance.getConst<bool>())
  {
    lemma = notQ;
  }
  else
  {
    lemma = nm->mkNode(Kind::OR, notQ, sInstance);
  }
  stat->incNumInstances();
  d_context.getStats().d_numInstances++;
  return lemma;
}


}  // namespace z3
}  // namespace cvc5::internal
