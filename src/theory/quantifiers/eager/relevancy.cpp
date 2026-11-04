/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Relevancy propagation.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_relevancy.cpp, and recast in cvc5 style.
 */

#include "theory/quantifiers/eager/relevancy.h"

#include "theory/quantifiers/eager/prop_core.h"
#include "theory/quantifiers/eager/quantifier_normalizer.h"
#include "theory/quantifiers/eager/smt_context.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

RelevancyPropagator::RelevancyPropagator(PropCore& core, SmtContext& theory)
    : d_core(core),
      d_theory(theory),
      d_qhead(0),
      d_relevantExprs(
          theory.getTrailStack().getContext(), true, UnmarkCleanup{this}),
      d_edges(
          theory.getTrailStack().getContext(), true, RemoveEdgeCleanup{this}),
      d_propagating(false)
{
}

RelevancyPropagator::~RelevancyPropagator() {}

void RelevancyPropagator::addDependency(TNode src, TNode target)
{
  if (isRelevant(src))
  {
    markAsRelevant(target);
    return;
  }
  d_dependents[src].push_back(target);
  d_edges.push_back(Edge{Edge::Kind::DEPENDENCY, src});
}

void RelevancyPropagator::addGateWatch(TNode child, bool val, TNode gate)
{
  Assert(gate.getKind() == Kind::AND || gate.getKind() == Kind::OR
         || gate.getKind() == Kind::IMPLIES || gate.getKind() == Kind::ITE);
  SatValue lval = d_core.findAssignment(child);
  if (!val)
  {
    lval = ~lval;
  }
  switch (lval)
  {
    case SAT_VALUE_FALSE: return;
    case SAT_VALUE_UNKNOWN:
    {
      size_t idx = val ? 1 : 0;
      d_gateWatches[idx][child].push_back(gate);
      if (child.getId() >= d_isWatched[idx].size())
      {
        d_isWatched[idx].resize(child.getId() + 1, false);
      }
      d_isWatched[idx][child.getId()] = true;
      d_edges.push_back(
          Edge{val ? Edge::Kind::POS_WATCH : Edge::Kind::NEG_WATCH, child});
      break;
    }
    case SAT_VALUE_TRUE:
      if (isRelevant(gate))
      {
        propagateRelevantGate(gate);
      }
      break;
  }
}

std::vector<TNode> RelevancyPropagator::getEdges(
    const std::unordered_map<TNode, std::vector<TNode>>& edges, TNode n)
{
  auto it = edges.find(n);
  if (it == edges.end())
  {
    return {};
  }
  return std::vector<TNode>(it->second.rbegin(), it->second.rend());
}

void RelevancyPropagator::removeEdge(const Edge& e)
{
  std::unordered_map<TNode, std::vector<TNode>>& edges =
      e.d_kind == Edge::Kind::DEPENDENCY
          ? d_dependents
          : d_gateWatches[e.d_kind == Edge::Kind::POS_WATCH ? 1 : 0];
  auto it = edges.find(e.d_node);
  Assert(it != edges.end() && !it->second.empty());
  it->second.pop_back();
  if (it->second.empty())
  {
    edges.erase(it);
  }
}

void RelevancyPropagator::setRelevant(TNode n)
{
  d_theory.getStats().d_numSetRelevant++;
  if (n.getId() >= d_isRelevant.size())
  {
    d_isRelevant.resize(n.getId() + 1, false);
  }
  d_isRelevant[n.getId()] = true;
  if (d_qhead > d_relevantExprs.size())
  {
    // the expressions past the end were popped
    d_qhead = d_relevantExprs.size();
  }
  d_relevantExprs.push_back(n);
  d_core.notifyRelevant(n);
}

void RelevancyPropagator::markAsRelevant(TNode n)
{
  if (!isRelevant(n))
  {
    TNode next = d_theory.getEGraph().getNextInEClass(n);
    if (!next.isNull())
    {
      // relevancy is shared by an entire equivalence class
      TNode curr = n;
      do
      {
        if (!isRelevant(curr))
        {
          setRelevant(curr);
        }
        curr = d_theory.getEGraph().getNextInEClass(curr);
      } while (curr != n);
    }
    else
    {
      setRelevant(n);
    }
  }
}

void RelevancyPropagator::propagateRelevantApp(TNode n)
{
  Assert(isRelevant(n));
  size_t j = n.getNumChildren();
  while (j > 0)
  {
    --j;
    markAsRelevant(n[j]);
  }
}

void RelevancyPropagator::propagateRelevantImplies(TNode n)
{
  Assert(n.getKind() == Kind::IMPLIES);
  SatValue val = d_core.findAssignment(n);
  // If val is SAT_VALUE_UNKNOWN then the expression is a root and no Boolean
  // variable was created for it.
  if (val == SAT_VALUE_UNKNOWN)
  {
    val = SAT_VALUE_TRUE;
  }
  switch (val)
  {
    case SAT_VALUE_FALSE: propagateRelevantApp(n); break;
    case SAT_VALUE_UNKNOWN: break;
    case SAT_VALUE_TRUE:
    {
      TNode arg0 = n[0];
      TNode arg1 = n[1];
      if (d_core.findAssignment(arg0) == SAT_VALUE_FALSE)
      {
        if (!isRelevant(arg0))
        {
          markAsRelevant(arg0);
        }
        return;
      }
      if (d_core.findAssignment(arg1) == SAT_VALUE_TRUE)
      {
        if (!isRelevant(arg1))
        {
          markAsRelevant(arg1);
        }
        return;
      }
      break;
    }
  }
}

void RelevancyPropagator::propagateRelevantOr(TNode n)
{
  Assert(n.getKind() == Kind::OR);
  SatValue val = d_core.findAssignment(n);
  // If val is SAT_VALUE_UNKNOWN then the expression is a root and no Boolean
  // variable was created for it.
  if (val == SAT_VALUE_UNKNOWN)
  {
    val = SAT_VALUE_TRUE;
  }
  switch (val)
  {
    case SAT_VALUE_FALSE: propagateRelevantApp(n); break;
    case SAT_VALUE_UNKNOWN: break;
    case SAT_VALUE_TRUE:
    {
      // only one true argument has to be relevant to justify the disjunction
      TNode trueArg;
      for (const Node& arg : n)
      {
        if (d_core.findAssignment(arg) == SAT_VALUE_TRUE)
        {
          if (isRelevant(arg))
          {
            return;
          }
          if (trueArg.isNull())
          {
            trueArg = arg;
          }
        }
      }
      if (!trueArg.isNull())
      {
        markAsRelevant(trueArg);
      }
      break;
    }
  }
}

void RelevancyPropagator::propagateRelevantAnd(TNode n)
{
  SatValue val = d_core.findAssignment(n);
  switch (val)
  {
    case SAT_VALUE_FALSE:
    {
      // only one false argument has to be relevant to refute the conjunction
      TNode falseArg;
      for (const Node& arg : n)
      {
        if (d_core.findAssignment(arg) == SAT_VALUE_FALSE)
        {
          if (isRelevant(arg))
          {
            return;
          }
          if (falseArg.isNull())
          {
            falseArg = arg;
          }
        }
      }
      if (!falseArg.isNull())
      {
        markAsRelevant(falseArg);
      }
      break;
    }
    case SAT_VALUE_UNKNOWN: break;
    case SAT_VALUE_TRUE: propagateRelevantApp(n); break;
  }
}

void RelevancyPropagator::propagateRelevantIte(TNode n)
{
  markAsRelevant(n[0]);
  switch (d_core.findAssignment(n[0]))
  {
    case SAT_VALUE_FALSE: markAsRelevant(n[2]); break;
    case SAT_VALUE_UNKNOWN: break;
    case SAT_VALUE_TRUE: markAsRelevant(n[1]); break;
  }
}

void RelevancyPropagator::propagateRelevantGate(TNode n)
{
  switch (n.getKind())
  {
    case Kind::OR: propagateRelevantOr(n); break;
    case Kind::AND: propagateRelevantAnd(n); break;
    case Kind::IMPLIES: propagateRelevantImplies(n); break;
    case Kind::ITE: propagateRelevantIte(n); break;
    default: propagateRelevantApp(n); break;
  }
}

void RelevancyPropagator::propagate()
{
  if (d_propagating)
  {
    return;
  }
  d_propagating = true;
  while (d_qhead < d_relevantExprs.size())
  {
    TNode n = d_relevantExprs[d_qhead];
    Assert(isRelevant(n));
    d_qhead++;
    if (eager::isApp(n))
    {
      propagateRelevantGate(n);
    }

    for (TNode target : getEdges(d_dependents, n))
    {
      markAsRelevant(target);
    }
  }
  d_propagating = false;
}

void RelevancyPropagator::notifyAssigned(TNode n, bool val)
{
  if (isRelevant(n))
  {
    switch (n.getKind())
    {
      case Kind::OR: propagateRelevantOr(n); break;
      case Kind::AND: propagateRelevantAnd(n); break;
      case Kind::IMPLIES: propagateRelevantImplies(n); break;
      default: break;
    }
  }
  size_t idx = val ? 1 : 0;
  if (n.getId() >= d_isWatched[idx].size() || !d_isWatched[idx][n.getId()])
  {
    return;
  }
  for (TNode gate : getEdges(d_gateWatches[idx], n))
  {
    if (isRelevant(gate))
    {
      propagateRelevantGate(gate);
    }
  }
}

void RelevancyPropagator::notifyMerge(TNode n1, TNode n2)
{
  if (isRelevant(n1))
  {
    markAsRelevant(n2);
    propagate();
  }
  else if (isRelevant(n2))
  {
    markAsRelevant(n1);
    propagate();
  }
}

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal
