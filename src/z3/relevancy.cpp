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

#include "z3/relevancy.h"

#include "z3/ast.h"
#include "z3/enode.h"
#include "z3/smt_context.h"

namespace cvc5::internal {
namespace z3 {

void RelevancyEh::markAsRelevant(RelevancyPropagator& rp, TNode n)
{
  rp.markAsRelevant(n);
}

void RelevancyEh::markArgsAsRelevant(RelevancyPropagator& rp, TNode n)
{
  size_t j = n.getNumChildren();
  while (j > 0)
  {
    --j;
    rp.markAsRelevant(n[j]);
  }
}

void SimpleRelevancyEh::operator()(RelevancyPropagator& rp)
{
  rp.markAsRelevant(d_target);
}

void PairRelevancyEh::operator()(RelevancyPropagator& rp)
{
  if (!rp.isRelevant(d_source1))
  {
    return;
  }
  if (!rp.isRelevant(d_source2))
  {
    return;
  }
  rp.markAsRelevant(d_target);
}

namespace {

class AndRelevancyEh : public RelevancyEh
{
 public:
  AndRelevancyEh(TNode p) : d_parent(p) {}
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

class OrRelevancyEh : public RelevancyEh
{
 public:
  OrRelevancyEh(TNode p) : d_parent(p) {}
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

class ImpliesRelevancyEh : public RelevancyEh
{
 public:
  ImpliesRelevancyEh(TNode p) : d_parent(p) {}
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

class IteRelevancyEh : public RelevancyEh
{
 public:
  IteRelevancyEh(TNode p) : d_parent(p) {}
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

class IteTermRelevancyEh : public RelevancyEh
{
 public:
  IteTermRelevancyEh(TNode p, TNode thenEq, TNode elseEq)
      : d_parent(p), d_thenEq(thenEq), d_elseEq(elseEq)
  {
  }
  void operator()(RelevancyPropagator& rp) override
  {
    if (!rp.isRelevant(d_parent))
    {
      return;
    }
    rp.markAsRelevant(d_parent[0]);
    switch (rp.getContext().getAssignment(d_parent[0]))
    {
      case L_FALSE: rp.markAsRelevant(d_elseEq); break;
      case L_UNDEF: break;
      case L_TRUE: rp.markAsRelevant(d_thenEq); break;
    }
  }

 private:
  TNode d_parent;
  TNode d_thenEq;
  TNode d_elseEq;
};

}  // namespace

RelevancyPropagator::RelevancyPropagator(SmtContext& ctx)
    : d_context(ctx), d_qhead(0), d_propagating(false)
{
}

RelevancyPropagator::~RelevancyPropagator() {}

bool RelevancyPropagator::enabled() const { return d_context.relevancy(); }

Region& RelevancyPropagator::getRegion() const { return d_context.getRegion(); }

void RelevancyPropagator::addDependency(TNode src, TNode target)
{
  if (!enabled())
  {
    return;
  }
  if (isRelevant(src))
  {
    markAsRelevant(target);
  }
  else
  {
    addHandler(src, mkRelevancyEh(SimpleRelevancyEh(target)));
  }
}

RelevancyEh* RelevancyPropagator::mkOrRelevancyEh(TNode n)
{
  Assert(n.getKind() == Kind::OR);
  return mkRelevancyEh(OrRelevancyEh(n));
}

RelevancyEh* RelevancyPropagator::mkImpliesRelevancyEh(TNode n)
{
  Assert(n.getKind() == Kind::IMPLIES);
  return mkRelevancyEh(ImpliesRelevancyEh(n));
}

RelevancyEh* RelevancyPropagator::mkAndRelevancyEh(TNode n)
{
  Assert(n.getKind() == Kind::AND);
  return mkRelevancyEh(AndRelevancyEh(n));
}

RelevancyEh* RelevancyPropagator::mkIteRelevancyEh(TNode n)
{
  Assert(n.getKind() == Kind::ITE);
  return mkRelevancyEh(IteRelevancyEh(n));
}

RelevancyEh* RelevancyPropagator::mkTermIteRelevancyEh(TNode c,
                                                       TNode t,
                                                       TNode e)
{
  return mkRelevancyEh(IteTermRelevancyEh(c, t, e));
}

RelevancyPropagator::RelevancyEhs* RelevancyPropagator::getHandlers(
    TNode n) const
{
  auto it = d_relevantEhs.find(n);
  return it == d_relevantEhs.end() ? nullptr : it->second;
}

void RelevancyPropagator::setHandlers(TNode n, RelevancyEhs* ehs)
{
  if (ehs == nullptr)
  {
    d_relevantEhs.erase(n);
  }
  else
  {
    d_relevantEhs[n] = ehs;
  }
}

RelevancyPropagator::RelevancyEhs* RelevancyPropagator::getWatches(
    TNode n, bool val) const
{
  size_t idx = val ? 1 : 0;
  if (!d_isWatched[idx].contains(n.getId()))
  {
    return nullptr;
  }
  auto it = d_watches[idx].find(n);
  return it == d_watches[idx].end() ? nullptr : it->second;
}

void RelevancyPropagator::setWatches(TNode n, bool val, RelevancyEhs* ehs)
{
  size_t idx = val ? 1 : 0;
  if (ehs == nullptr)
  {
    d_watches[idx].erase(n);
  }
  else
  {
    d_watches[idx][n] = ehs;
    d_isWatched[idx].insert(n.getId());
  }
}

void RelevancyPropagator::addHandler(TNode source, RelevancyEh* eh)
{
  if (!enabled())
  {
    return;
  }
  if (isRelevantCore(source))
  {
    eh->operator()(*this, source);
  }
  else
  {
    Assert(eh != nullptr);
    d_trail.push_back(EhTrail(source));
    setHandlers(source,
                new (getRegion()) RelevancyEhs(eh, getHandlers(source)));
  }
}

void RelevancyPropagator::addWatch(TNode n, bool val, RelevancyEh* eh)
{
  if (!enabled())
  {
    return;
  }
  LBool lval = d_context.findAssignment(n);
  if (!val)
  {
    lval = ~lval;
  }
  switch (lval)
  {
    case L_FALSE: return;
    case L_UNDEF:
      Assert(eh != nullptr);
      setWatches(
          n, val, new (getRegion()) RelevancyEhs(eh, getWatches(n, val)));
      d_trail.push_back(EhTrail(n, val));
      break;
    case L_TRUE: eh->operator()(*this, n, val); break;
  }
}

void RelevancyPropagator::addWatch(TNode n, bool val, TNode target)
{
  if (!enabled())
  {
    return;
  }
  LBool lval = d_context.findAssignment(n);
  if (!val)
  {
    lval = ~lval;
  }
  switch (lval)
  {
    case L_FALSE: return;
    case L_UNDEF:
      addWatch(n, val, mkRelevancyEh(SimpleRelevancyEh(target)));
      break;
    case L_TRUE:
      markAsRelevant(target);
      propagate();
      break;
  }
}

void RelevancyPropagator::push()
{
  d_scopes.push_back(Scope{d_relevantExprs.size(), d_trail.size()});
}

void RelevancyPropagator::pop(size_t numScopes)
{
  size_t lvl = d_scopes.size();
  Assert(numScopes <= lvl);
  size_t newLvl = lvl - numScopes;
  Scope& s = d_scopes[newLvl];
  unmarkRelevantExprs(s.d_relevantExprsLim);
  undoTrail(s.d_trailLim);
  d_scopes.resize(newLvl);
}

void RelevancyPropagator::unmarkRelevantExprs(size_t oldLim)
{
  Assert(oldLim <= d_relevantExprs.size());
  size_t i = d_relevantExprs.size();
  while (i != oldLim)
  {
    --i;
    d_isRelevant.remove(d_relevantExprs[i].getId());
  }
  d_relevantExprs.resize(oldLim);
  d_qhead = d_relevantExprs.size();
}

void RelevancyPropagator::undoTrail(size_t oldLim)
{
  Assert(oldLim <= d_trail.size());
  size_t i = d_trail.size();
  while (i != oldLim)
  {
    --i;
    EhTrail& t = d_trail[i];
    TNode n = t.getNode();
    RelevancyEhs* ehs;
    switch (t.getKind())
    {
      case EhTrail::Kind::POS_WATCH:
        ehs = getWatches(n, true);
        Assert(ehs != nullptr);
        setWatches(n, true, ehs->tail());
        break;
      case EhTrail::Kind::NEG_WATCH:
        ehs = getWatches(n, false);
        Assert(ehs != nullptr);
        setWatches(n, false, ehs->tail());
        break;
      case EhTrail::Kind::HANDLER:
        ehs = getHandlers(n);
        Assert(ehs != nullptr);
        setHandlers(n, ehs->tail());
        break;
    }
  }
  d_trail.erase(d_trail.begin() + oldLim, d_trail.end());
}

void RelevancyPropagator::setRelevant(TNode n)
{
  d_context.getStats().d_numSetRelevant++;
  d_isRelevant.insert(n.getId());
  d_relevantExprs.push_back(n);
  d_context.relevantEh(n);
}

void RelevancyPropagator::markAndPropagate(TNode n)
{
  if (!enabled())
  {
    return;
  }
  if (!isRelevantCore(n))
  {
    markAsRelevant(n);
    propagate();
  }
}

void RelevancyPropagator::markAsRelevant(TNode n)
{
  if (!enabled())
  {
    return;
  }
  if (!isRelevantCore(n))
  {
    ENode* e = d_context.findENode(n);
    if (e != nullptr)
    {
      // relevancy is shared by an entire equivalence class
      ENode* curr = e;
      do
      {
        if (!isRelevantCore(curr->getExpr()))
        {
          setRelevant(curr->getExpr());
        }
        curr = curr->getNext();
      } while (curr != e);
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
  LBool val = d_context.findAssignment(n);
  // If val is L_UNDEF then the expression is a root and no Boolean variable
  // was created for it.
  if (val == L_UNDEF)
  {
    val = L_TRUE;
  }
  switch (val)
  {
    case L_FALSE: propagateRelevantApp(n); break;
    case L_UNDEF: break;
    case L_TRUE:
    {
      TNode arg0 = n[0];
      TNode arg1 = n[1];
      if (d_context.findAssignment(arg0) == L_FALSE)
      {
        if (!isRelevantCore(arg0))
        {
          markAsRelevant(arg0);
        }
        return;
      }
      if (d_context.findAssignment(arg1) == L_TRUE)
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
  LBool val = d_context.findAssignment(n);
  // If val is L_UNDEF then the expression is a root and no Boolean variable
  // was created for it.
  if (val == L_UNDEF)
  {
    val = L_TRUE;
  }
  switch (val)
  {
    case L_FALSE: propagateRelevantApp(n); break;
    case L_UNDEF: break;
    case L_TRUE:
    {
      // only one true argument has to be relevant to justify the disjunction
      TNode trueArg;
      for (const Node& arg : n)
      {
        if (d_context.findAssignment(arg) == L_TRUE)
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
  LBool val = d_context.findAssignment(n);
  switch (val)
  {
    case L_FALSE:
    {
      // only one false argument has to be relevant to refute the conjunction
      TNode falseArg;
      for (const Node& arg : n)
      {
        if (d_context.findAssignment(arg) == L_FALSE)
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
    case L_UNDEF: break;
    case L_TRUE: propagateRelevantApp(n); break;
  }
}

void RelevancyPropagator::propagateRelevantIte(TNode n)
{
  markAsRelevant(n[0]);
  switch (d_context.findAssignment(n[0]))
  {
    case L_FALSE: markAsRelevant(n[2]); break;
    case L_UNDEF: break;
    case L_TRUE: markAsRelevant(n[1]); break;
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

    RelevancyEhs* ehs = getHandlers(n);
    while (ehs != nullptr)
    {
      ehs->head()->operator()(*this, n);
      ehs = ehs->tail();
    }
  }
  d_propagating = false;
}

void RelevancyPropagator::assignEh(TNode n, bool val)
{
  if (!enabled())
  {
    return;
  }
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
  RelevancyEhs* ehs = getWatches(n, val);
  while (ehs != nullptr)
  {
    ehs->head()->operator()(*this, n, val);
    ehs = ehs->tail();
  }
}

void RelevancyPropagator::print(std::ostream& out) const
{
  if (enabled() && !d_relevantExprs.empty())
  {
    out << "relevant exprs:\n";
    for (const Node& n : d_relevantExprs)
    {
      out << "#" << n.getId() << " ";
    }
    out << "\n";
  }
}

}  // namespace z3
}  // namespace cvc5::internal
