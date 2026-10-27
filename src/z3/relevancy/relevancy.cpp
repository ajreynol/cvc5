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

#include "z3/relevancy/relevancy.h"

#include "z3/relevancy/prop_core.h"
#include "z3/util/ast.h"

namespace cvc5::internal {
namespace z3 {

void SimpleRelevancyHandler::operator()(RelevancyPropagator& rp)
{
  rp.markAsRelevant(d_target);
}

namespace {

class AndRelevancyHandler : public RelevancyHandler
{
 public:
  AndRelevancyHandler(TNode p) : d_parent(p) {}
  void operator()(RelevancyPropagator& rp) override
  {
    if (rp.isRelevant(d_parent))
    {
      rp.propagateRelevantAnd(d_parent);
    }
  }

 private:
  TNode d_parent;
};

class OrRelevancyHandler : public RelevancyHandler
{
 public:
  OrRelevancyHandler(TNode p) : d_parent(p) {}
  void operator()(RelevancyPropagator& rp) override
  {
    if (rp.isRelevant(d_parent))
    {
      rp.propagateRelevantOr(d_parent);
    }
  }

 private:
  TNode d_parent;
};

class ImpliesRelevancyHandler : public RelevancyHandler
{
 public:
  ImpliesRelevancyHandler(TNode p) : d_parent(p) {}
  void operator()(RelevancyPropagator& rp) override
  {
    if (rp.isRelevant(d_parent))
    {
      rp.propagateRelevantImplies(d_parent);
    }
  }

 private:
  TNode d_parent;
};

class IteRelevancyHandler : public RelevancyHandler
{
 public:
  IteRelevancyHandler(TNode p) : d_parent(p) {}
  void operator()(RelevancyPropagator& rp) override
  {
    if (rp.isRelevant(d_parent))
    {
      rp.propagateRelevantIte(d_parent);
    }
  }

 private:
  TNode d_parent;
};

class IteTermRelevancyHandler : public RelevancyHandler
{
 public:
 private:
  TNode d_parent;
  TNode d_thenEq;
  TNode d_elseEq;
};

}  // namespace

RelevancyPropagator::RelevancyPropagator(PropCore& core, TheorySide& theory)
    : d_core(core),
      d_theory(theory),
      d_qhead(0),
      d_relevantExprs(
          theory.getTrailStack().getContext(), true, UnmarkCleanup{this}),
      d_trail(
          theory.getTrailStack().getContext(), true, UndoHandlerCleanup{this}),
      d_propagating(false)
{
}

RelevancyPropagator::~RelevancyPropagator() {}

TrailStack& RelevancyPropagator::getTrailStack() const
{
  return d_theory.getTrailStack();
}

void RelevancyPropagator::addDependency(TNode src, TNode target)
{
  if (isRelevant(src))
  {
    markAsRelevant(target);
  }
  else
  {
    addHandler(src, mkRelevancyHandler(SimpleRelevancyHandler(target)));
  }
}

RelevancyHandler* RelevancyPropagator::mkOrRelevancyHandler(TNode n)
{
  Assert(n.getKind() == Kind::OR);
  return mkRelevancyHandler(OrRelevancyHandler(n));
}

RelevancyHandler* RelevancyPropagator::mkImpliesRelevancyHandler(TNode n)
{
  Assert(n.getKind() == Kind::IMPLIES);
  return mkRelevancyHandler(ImpliesRelevancyHandler(n));
}

RelevancyHandler* RelevancyPropagator::mkAndRelevancyHandler(TNode n)
{
  Assert(n.getKind() == Kind::AND);
  return mkRelevancyHandler(AndRelevancyHandler(n));
}

RelevancyHandler* RelevancyPropagator::mkIteRelevancyHandler(TNode n)
{
  Assert(n.getKind() == Kind::ITE);
  return mkRelevancyHandler(IteRelevancyHandler(n));
}

RelevancyPropagator::RelevancyHandlers* RelevancyPropagator::getHandlers(
    TNode n) const
{
  auto it = d_relevantHandlers.find(n);
  return it == d_relevantHandlers.end() ? nullptr : it->second;
}

void RelevancyPropagator::setHandlers(TNode n, RelevancyHandlers* ehs)
{
  if (ehs == nullptr)
  {
    d_relevantHandlers.erase(n);
  }
  else
  {
    d_relevantHandlers[n] = ehs;
  }
}

RelevancyPropagator::RelevancyHandlers* RelevancyPropagator::getWatches(
    TNode n, bool val) const
{
  size_t idx = val ? 1 : 0;
  size_t id = n.getId();
  if (id >= d_isWatched[idx].size() || !d_isWatched[idx][id])
  {
    return nullptr;
  }
  auto it = d_watches[idx].find(n);
  return it == d_watches[idx].end() ? nullptr : it->second;
}

void RelevancyPropagator::setWatches(TNode n, bool val, RelevancyHandlers* ehs)
{
  size_t idx = val ? 1 : 0;
  if (ehs == nullptr)
  {
    d_watches[idx].erase(n);
  }
  else
  {
    d_watches[idx][n] = ehs;
    if (n.getId() >= d_isWatched[idx].size())
    {
      d_isWatched[idx].resize(n.getId() + 1, false);
    }
    d_isWatched[idx][n.getId()] = true;
  }
}

void RelevancyPropagator::addHandler(TNode source, RelevancyHandler* eh)
{
  if (isRelevantCore(source))
  {
    eh->operator()(*this, source);
  }
  else
  {
    Assert(eh != nullptr);
    d_trail.push_back(HandlerTrail(source));
    setHandlers(source,
                new (getTrailStack())
                    RelevancyHandlers(eh, getHandlers(source)));
  }
}

void RelevancyPropagator::addWatch(TNode n, bool val, RelevancyHandler* eh)
{
  SatValue lval = d_core.findAssignment(n);
  if (!val)
  {
    lval = ~lval;
  }
  switch (lval)
  {
    case SAT_VALUE_FALSE: return;
    case SAT_VALUE_UNKNOWN:
      Assert(eh != nullptr);
      setWatches(n,
                 val,
                 new (getTrailStack())
                     RelevancyHandlers(eh, getWatches(n, val)));
      d_trail.push_back(HandlerTrail(n, val));
      break;
    case SAT_VALUE_TRUE: eh->operator()(*this, n, val); break;
  }
}

void RelevancyPropagator::undoHandler(const HandlerTrail& t)
{
  TNode n = t.getNode();
  RelevancyHandlers* ehs;
  switch (t.getKind())
  {
    case HandlerTrail::Kind::POS_WATCH:
      ehs = getWatches(n, true);
      Assert(ehs != nullptr);
      setWatches(n, true, ehs->tail());
      break;
    case HandlerTrail::Kind::NEG_WATCH:
      ehs = getWatches(n, false);
      Assert(ehs != nullptr);
      setWatches(n, false, ehs->tail());
      break;
    case HandlerTrail::Kind::HANDLER:
      ehs = getHandlers(n);
      Assert(ehs != nullptr);
      setHandlers(n, ehs->tail());
      break;
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
  if (!isRelevantCore(n))
  {
    TNode next = d_theory.getNextInEClass(n);
    if (!next.isNull())
    {
      // relevancy is shared by an entire equivalence class
      TNode curr = n;
      do
      {
        if (!isRelevantCore(curr))
        {
          setRelevant(curr);
        }
        curr = d_theory.getNextInEClass(curr);
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
  Assert(isRelevantCore(n));
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
        if (!isRelevantCore(arg0))
        {
          markAsRelevant(arg0);
        }
        return;
      }
      if (d_core.findAssignment(arg1) == SAT_VALUE_TRUE)
      {
        if (!isRelevantCore(arg1))
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
          if (isRelevantCore(arg))
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
          if (isRelevantCore(arg))
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
    Assert(isRelevantCore(n));
    d_qhead++;
    if (z3::isApp(n))
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

    RelevancyHandlers* ehs = getHandlers(n);
    while (ehs != nullptr)
    {
      ehs->head()->operator()(*this, n);
      ehs = ehs->tail();
    }
  }
  d_propagating = false;
}

void RelevancyPropagator::notifyAssigned(TNode n, bool val)
{
  if (isRelevantCore(n))
  {
    switch (n.getKind())
    {
      case Kind::OR: propagateRelevantOr(n); break;
      case Kind::AND: propagateRelevantAnd(n); break;
      case Kind::IMPLIES: propagateRelevantImplies(n); break;
      default: break;
    }
  }
  RelevancyHandlers* ehs = getWatches(n, val);
  while (ehs != nullptr)
  {
    ehs->head()->operator()(*this, n, val);
    ehs = ehs->tail();
  }
}

}  // namespace z3
}  // namespace cvc5::internal
