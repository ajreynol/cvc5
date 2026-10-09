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

#include "z3/qi_queue.h"

#include <algorithm>
#include <fstream>
#include <unordered_map>

#include "base/output.h"
#include "expr/node_manager.h"
#include "options/z3_options.h"
#include "smt/env.h"
#include "z3/ast.h"
#include "z3/enode.h"
#include "z3/quantifier_manager.h"
#include "z3/smt_context.h"

namespace cvc5::internal {
namespace z3 {

QiQueue::QiQueue(QuantifierManager& qm, SmtContext& ctx, Params& params)
    : d_qm(qm),
      d_context(ctx),
      d_params(params),
      d_checker(ctx),
      d_eagerCostThreshold(0)
{
  d_vals.resize(CV_NUM_VARS, 0.0f);
}

void QiQueue::setup()
{
  if (!d_costFunction.parse(d_params.d_qiCost))
  {
    Warning() << "z3: invalid cost function '" << d_params.d_qiCost
              << "', switching to the default one" << std::endl;
    bool ok = d_costFunction.parse("(+ weight generation)");
    AlwaysAssert(ok);
  }
  if (!d_newGenFunction.parse(d_params.d_qiNewGen))
  {
    Warning() << "z3: invalid new-generation function '" << d_params.d_qiNewGen
              << "', switching to the default one" << std::endl;
    bool ok = d_newGenFunction.parse("cost");
    AlwaysAssert(ok);
  }
  d_eagerCostThreshold = d_params.d_qiEagerThreshold;
}

TNode QiQueue::getQuantifier(Fingerprint* f) const
{
  return d_qm.getQuantifierById(f->getData());
}

QuantifierStat* QiQueue::setValues(TNode q,
                                   TNode pat,
                                   uint32_t generation,
                                   uint32_t minTopGeneration,
                                   uint32_t maxTopGeneration,
                                   float cost)
{
  QuantifierStat* stat = d_qm.getStat(q);
  d_vals[CV_COST] = cost;
  d_vals[CV_MIN_TOP_GENERATION] = static_cast<float>(minTopGeneration);
  d_vals[CV_MAX_TOP_GENERATION] = static_cast<float>(maxTopGeneration);
  d_vals[CV_INSTANCES] = static_cast<float>(stat->getNumInstancesCurrBranch());
  d_vals[CV_SIZE] = static_cast<float>(stat->getSize());
  d_vals[CV_DEPTH] = static_cast<float>(stat->getDepth());
  d_vals[CV_GENERATION] = static_cast<float>(generation);
  d_vals[CV_QUANT_GENERATION] = static_cast<float>(stat->getGeneration());
  d_vals[CV_WEIGHT] = static_cast<float>(getWeight(q));
  d_vals[CV_VARS] = static_cast<float>(getNumDecls(q));
  d_vals[CV_PATTERN_WIDTH] =
      pat.isNull() ? 1.0f : static_cast<float>(pat.getNumChildren());
  d_vals[CV_TOTAL_INSTANCES] =
      static_cast<float>(stat->getNumInstancesCurrSearch());
  d_vals[CV_SCOPE] = static_cast<float>(d_context.getScopeLevel());
  d_vals[CV_NESTED_QUANTIFIERS] =
      static_cast<float>(stat->getNumNestedQuantifiers());
  d_vals[CV_CS_FACTOR] = static_cast<float>(stat->getCaseSplitFactor());
  return stat;
}

float QiQueue::getCost(TNode q,
                       TNode pat,
                       uint32_t generation,
                       uint32_t minTopGeneration,
                       uint32_t maxTopGeneration)
{
  QuantifierStat* stat =
      setValues(q, pat, generation, minTopGeneration, maxTopGeneration, 0);
  float r = d_costFunction(d_vals);
  stat->updateMaxCost(r);
  return r;
}

uint32_t QiQueue::getNewGen(TNode q, uint32_t generation, float cost)
{
  // The top generations are not available when the new generation is computed.
  setValues(q, TNode::null(), generation, 0, 0, cost);
  float r = d_newGenFunction(d_vals);
  if (getWeight(q) > 0 || r > 0)
  {
    return static_cast<uint32_t>(r);
  }
  return std::max(generation + 1, static_cast<uint32_t>(r));
}

void QiQueue::insert(Fingerprint* f,
                     TNode pat,
                     uint32_t generation,
                     uint32_t minTopGeneration,
                     uint32_t maxTopGeneration)
{
  TNode q = getQuantifier(f);
  float cost = getCost(q, pat, generation, minTopGeneration, maxTopGeneration);
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
    if (d_stats.d_numInstances > d_params.d_qiMaxInstances)
    {
      d_context.setReasonUnknown(
          "the maximum number of quantifier instances was reached");
      break;
    }
    Fingerprint* f = curr.d_qb;
    TNode qa = getQuantifier(f);

    if (curr.d_cost <= d_eagerCostThreshold)
    {
      instantiate(curr);
    }
    else if (d_params.d_qiPromoteUnsat
             && d_checker.isUnsat(
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

  if (d_context.getEnv().getOptions().z3.z3QiChecker
      && d_checker.isSat(getQuantBody(q), numBindings, bindings))
  {
    // The instance is already satisfied, so creating it would be wasted
    // work. It still counts as an instantiation, as it does in Z3.
    stat->incNumInstancesCheckerSat();
    d_context.getStats().d_numInstancesCheckerSat++;
    return;
  }

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
  const std::string& dumpTo =
      d_context.getEnv().getOptions().z3.z3DumpInstances;
  if (!dumpTo.empty())
  {
    // One line per instance, before the rewriter runs, which is the point at
    // which Z3's qi_queue trace prints its "new instance".
    std::ofstream out(dumpTo, std::ios::app);
    out << instance << "\n";
  }
  if (d_context.d_inForcedRematch)
  {
    Trace("z3-qi-missed") << "MISSED q" << q.getId() << " " << instance
                          << std::endl;
  }
  Node sInstance = d_context.rewriteInstance(instance);

  if (sInstance.getKind() == Kind::CONST_BOOLEAN && sInstance.getConst<bool>())
  {
    stat->incNumInstancesSimplifyTrue();
    d_context.getStats().d_numInstancesSimplifyTrue++;
    return;
  }

  stat->incNumInstances();

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
  d_instances.push_back(lemma);
  d_stats.d_numInstances++;
  d_context.getStats().d_numInstances++;
  uint32_t gen = getNewGen(q, generation, ent.d_cost);
  Trace("z3-qi") << "[instance] q" << q.getId() << " nargs " << numBindings
                 << " gen " << generation << " cost " << ent.d_cost
                 << " newgen " << gen << std::endl;
  Trace("z3-qi-lemma") << "  lemma: " << lemma << std::endl;
  d_context.internalizeInstance(lemma, gen);
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

void QiQueue::reset()
{
  d_newEntries.clear();
  d_delayedEntries.clear();
  d_instances.clear();
  d_scopes.clear();
}

void QiQueue::initSearchEh() { d_newEntries.clear(); }

bool QiQueue::finalCheckEh()
{
  if (d_params.d_qiConservativeFinalCheck)
  {
    // Only the cheapest of the delayed instances are created.
    bool init = false;
    float minCost = 0.0;
    size_t sz = d_delayedEntries.size();
    for (size_t i = 0; i < sz; ++i)
    {
      Entry& e = d_delayedEntries[i];
      if (!e.d_instantiated && e.d_cost <= d_params.d_qiLazyThreshold
          && (!init || e.d_cost < minCost))
      {
        init = true;
        minCost = e.d_cost;
      }
    }
    bool result = true;
    for (size_t i = 0; i < sz; ++i)
    {
      Entry& e = d_delayedEntries[i];
      if (!e.d_instantiated && e.d_cost <= minCost)
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

  bool result = true;
  for (size_t i = 0; i < d_delayedEntries.size(); ++i)
  {
    Entry& e = d_delayedEntries[i];
    if (!e.d_instantiated && e.d_cost <= d_params.d_qiLazyThreshold)
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

void QiQueue::printDelayedInstancesStats(std::ostream& out) const
{
  std::unordered_map<Node, DelayedQaInfo> qa2Info;
  std::vector<Node> qas;
  for (const Entry& e : d_delayedEntries)
  {
    if (e.d_instantiated)
    {
      continue;
    }
    Node qa = getQuantifier(e.d_qb);
    auto it = qa2Info.find(qa);
    if (it != qa2Info.end())
    {
      it->second.d_num++;
      it->second.d_minCost = std::min(it->second.d_minCost, e.d_cost);
      it->second.d_maxCost = std::max(it->second.d_maxCost, e.d_cost);
    }
    else
    {
      qas.push_back(qa);
      DelayedQaInfo info;
      info.d_num = 1;
      info.d_minCost = e.d_cost;
      info.d_maxCost = e.d_cost;
      qa2Info[qa] = info;
    }
  }
  for (const Node& qa : qas)
  {
    const DelayedQaInfo& info = qa2Info[qa];
    out << getQid(qa) << ": " << info.d_num << " [" << info.d_minCost << ", "
        << info.d_maxCost << "]\n";
  }
}

void QiQueue::getMinMaxCosts(float& min, float& max) const
{
  min = 0.0f;
  max = 0.0f;
  bool found = false;
  for (const Entry& e : d_delayedEntries)
  {
    if (!e.d_instantiated)
    {
      float c = e.d_cost;
      if (found)
      {
        min = std::min(min, c);
        max = std::max(max, c);
      }
      else
      {
        found = true;
        min = c;
        max = c;
      }
    }
  }
}

}  // namespace z3
}  // namespace cvc5::internal
