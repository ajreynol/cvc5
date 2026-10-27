/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The Boolean search of the ported Z3 core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), the
 * Boolean part of files src/smt/smt_context.cpp and
 * src/smt/smt_internalizer.cpp, and recast in cvc5 style.
 */

#include "z3/relevancy/prop_core.h"

#include <algorithm>

#include "base/output.h"
#include "expr/node_algorithm.h"
#include "expr/node_manager.h"
#include "smt/env.h"
#include "util/resource_manager.h"

namespace cvc5::internal {
namespace z3 {

namespace {

bool isTrueNode(TNode n)
{
  return n.getKind() == Kind::CONST_BOOLEAN && n.getConst<bool>();
}

bool isFalseNode(TNode n)
{
  return n.getKind() == Kind::CONST_BOOLEAN && !n.getConst<bool>();
}

/** True if n is an atom or the negation of one, as Z3's is_literal is. */
bool isLiteralNode(TNode n)
{
  TNode a = n.getKind() == Kind::NOT ? n[0] : n;
  return !isApp(a) || a.getNumChildren() == 0;
}

}  // namespace

PropCore::PropCore(Env& env, TheorySide& ctx, Statistics& stats)
    : EnvObj(env),
      d_ctx(ctx),
      d_stats(stats),
      d_relevancyPropagator(new RelevancyPropagator(*this, ctx)),
      d_qhead(0),
      d_conflict(false),
      d_assertedInconsistent(false),
      d_flushing(false),
      d_assertedFormulasQhead(0),
      d_hasQuantifiers(false),
      d_internalizingAssertions(false),
      d_searching(false),
      d_resourceOut(false),
      d_scopeLvl(0),
      d_mkBoolVarTrail(*this)
{
}

PropCore::~PropCore() {}

void PropCore::initTrue(TNode t)
{
  mkBoolVar(t);
  Assert(getBoolVar(t) == s_trueBoolVar);
  Assert(s_trueLiteral.var() == s_trueBoolVar);
  d_assignment[s_trueLiteral.index()] = SAT_VALUE_TRUE;
  d_assignment[s_falseLiteral.index()] = SAT_VALUE_FALSE;
}

void PropCore::flushClauses()
{
  d_flushing = true;
  delClauses(d_auxClauses, 0);
  d_flushing = false;
}

// ---------------------------------------------------- input and entry points

void PropCore::assertFormula(TNode e)
{
  if (getCancelFlag())
  {
    return;
  }
  if (!d_searching)
  {
    popToBaseLvl();
  }
  pushAssertion(e);
}

void PropCore::pushAssertion(TNode e)
{
  // Z3 splits a conjunction, and a negated disjunction, into separate
  // assertions while they are being collected (see
  // asserted_formulas::push_assertion). This matters beyond saving a Boolean
  // variable: an assertion is marked relevant when it is asserted, while the
  // conjuncts of a top-level conjunction never are -- the and-gate only
  // propagates relevancy to its arguments once the conjunction itself is
  // assigned, which never happens for a root. cvc5's preprocessor leaves
  // such conjunctions in place, so the split is done here.
  if (isTrueNode(e))
  {
    return;
  }
  if (isFalseNode(e))
  {
    d_assertedInconsistent = true;
    d_assertedFormulas.push_back(e);
    return;
  }
  if (e.getKind() == Kind::AND)
  {
    for (const Node& arg : e)
    {
      pushAssertion(arg);
    }
    return;
  }
  if (e.getKind() == Kind::NOT && e[0].getKind() == Kind::OR)
  {
    for (const Node& arg : e[0])
    {
      pushAssertion(arg.negate());
    }
    return;
  }
  // What Z3 does next is asserted_formulas::flatten_clauses, whose point is
  // that its core gets flat clauses rather than a tree of gates: every nested
  // gate costs a Boolean variable, two clauses and a link in the chain
  // relevancy has to walk before it reaches the atoms. A top-level
  // if-then-else is two clauses, and a top-level disjunction over a
  // conjunction distributes.
  if (e.getKind() == Kind::ITE)
  {
    pushAssertion(nodeManager()->mkNode(Kind::OR, e[0].negate(), e[1]));
    pushAssertion(nodeManager()->mkNode(Kind::OR, Node(e[0]), e[2]));
    return;
  }
  if (e.getKind() == Kind::OR && e.getNumChildren() == 2)
  {
    for (size_t i = 0; i < 2; ++i)
    {
      TNode conj = e[i];
      TNode rest = e[1 - i];
      // Z3 also distributes over a shared conjunction when the other side is
      // not a literal, using a reference count to tell that the conjunction
      // occurs nowhere else. There is no equally cheap test here, so only the
      // case that cannot grow the formula is taken: duplicating a literal
      // across the conjuncts costs one literal per conjunct.
      if (conj.getKind() == Kind::AND && isLiteralNode(rest))
      {
        for (const Node& arg : conj)
        {
          pushAssertion(nodeManager()->mkNode(Kind::OR, Node(rest), arg));
        }
        return;
      }
    }
  }
  if (!d_hasQuantifiers && expr::hasClosure(Node(e)))
  {
    d_hasQuantifiers = true;
  }
  Trace("z3-assert") << "ASSERT " << e << std::endl;
  d_assertedFormulas.push_back(e);
}

void PropCore::internalizeAssertions()
{
  if (getCancelFlag() || d_internalizingAssertions)
  {
    return;
  }
  d_internalizingAssertions = true;
  if (d_assertedInconsistent)
  {
    setConflict();
    d_internalizingAssertions = false;
    return;
  }
  while (d_assertedFormulasQhead < d_assertedFormulas.size())
  {
    if (getCancelFlag())
    {
      d_internalizingAssertions = false;
      return;
    }
    TNode f = d_assertedFormulas[d_assertedFormulasQhead];
    ++d_assertedFormulasQhead;
    d_ctx.internalizeAssertion(f, 0);
  }
  d_internalizingAssertions = false;
}

// ----------------------------------------------------------- the fixpoint

bool PropCore::getCancelFlag()
{
  if (!resourceManager()->out())
  {
    return false;
  }
  d_resourceOut = true;
  return true;
}

bool PropCore::resourceLimitsExceeded()
{
  if (d_searching && d_resourceOut)
  {
    return true;
  }
  return getCancelFlag();
}

bool PropCore::canPropagate() const
{
  return d_qhead != d_assignedLiterals.size()
         || d_relevancyPropagator->canPropagate()
         || d_ctx.hasPendingTheoryWork();
}

bool PropCore::propagate()
{
  while (true)
  {
    if (inconsistent())
    {
      return false;
    }
    size_t qhead = d_qhead;
    if (!bcp())
    {
      return false;
    }
    Assert(!inconsistent());
    propagateRelevancy(qhead);
    if (inconsistent())
    {
      return false;
    }
    if (!d_ctx.theoryPropagate())
    {
      return false;
    }
    if (resourceLimitsExceeded())
    {
      d_qhead = qhead;
      return true;
    }
    if (!canPropagate())
    {
      return true;
    }
  }
}

// ------------------------------------------------- the Boolean structure

void PropCore::assertRoot(TNode n)
{
  if (isGate(n))
  {
    switch (n.getKind())
    {
      case Kind::AND:
      {
        for (const Node& arg : n)
        {
          d_ctx.internalizeRec(arg, true);
          Literal lit = getLiteral(arg);
          mkRootClause(1, &lit);
        }
        break;
      }
      case Kind::OR:
      {
        LiteralVector lits;
        for (const Node& arg : n)
        {
          d_ctx.internalizeRec(arg, true);
          lits.push_back(getLiteral(arg));
        }
        mkRootClause(lits.size(), lits.data());
        addOrRelWatches(n);
        break;
      }
      case Kind::IMPLIES:
      {
        d_ctx.internalizeRec(n[0], true);
        d_ctx.internalizeRec(n[1], true);
        mkRootClause(~getLiteral(n[0]), getLiteral(n[1]));
        addImpliesRelWatches(n);
        break;
      }
      case Kind::EQUAL:
      case Kind::XOR:
      {
        TNode lhs = n[0];
        TNode rhs = n[1];
        d_ctx.internalizeRec(lhs, true);
        d_ctx.internalizeRec(rhs, true);
        Literal l1 = getLiteral(lhs);
        Literal l2 = getLiteral(rhs);
        if (n.getKind() == Kind::XOR)
        {
          l2 = ~l2;
        }
        mkRootClause(l1, ~l2);
        mkRootClause(~l1, l2);
        break;
      }
      case Kind::ITE:
      {
        TNode c = n[0];
        TNode t = n[1];
        TNode e = n[2];
        d_ctx.internalizeRec(c, true);
        d_ctx.internalizeRec(t, true);
        d_ctx.internalizeRec(e, true);
        Literal cl = getLiteral(c);
        Literal tl = getLiteral(t);
        Literal el = getLiteral(e);
        mkRootClause(~cl, tl);
        mkRootClause(cl, el);
        addIteRelWatches(n);
        break;
      }
      default: Unreachable();
    }
    markAsRelevant(n);
  }
  else if (n.getKind() == Kind::DISTINCT)
  {
    // Z3 encodes a very large distinct with auxiliary values over a fresh
    // sort. cvc5's rewriter expands distinct during preprocessing, so the
    // core is not expected to meet one at all; the plain encoding is used.
    assertDefault(n);
    markAsRelevant(n);
  }
  else
  {
    assertDefault(n);
  }
}

void PropCore::mkGateConstraints(TNode n)
{
  switch (n.getKind())
  {
    case Kind::NOT: mkNotCnstr(n); break;
    case Kind::AND:
      mkAndCnstr(n);
      addAndRelWatches(n);
      break;
    case Kind::OR:
      mkOrCnstr(n);
      addOrRelWatches(n);
      break;
    case Kind::IMPLIES:
      mkImpliesCnstr(n);
      addImpliesRelWatches(n);
      break;
    case Kind::EQUAL:
      if (n[0].getType().isBoolean())
      {
        mkIffCnstr(n, false);
      }
      break;
    case Kind::ITE:
      mkIteCnstr(n);
      addIteRelWatches(n);
      break;
    case Kind::XOR: mkIffCnstr(n, true); break;
    case Kind::CONST_BOOLEAN: break;
    case Kind::DISTINCT:
      Unreachable() << "z3: formula has not been simplified: " << n;
    default: break;
  }
}

void PropCore::assertDefault(TNode n)
{
  d_ctx.internalize(n, true);
  Literal l = getLiteral(n);
  if (l == s_falseLiteral)
  {
    setConflict();
  }
  else if (l == s_trueLiteral)
  {
    return;
  }
  else
  {
    assign(l);
    markAsRelevant(l);
  }
}

void PropCore::mkGateClause(size_t numLits, Literal* lits)
{
  mkClause(numLits, lits);
}

void PropCore::mkGateClause(Literal l1, Literal l2)
{
  Literal ls[2] = {l1, l2};
  mkGateClause(2, ls);
}

void PropCore::mkGateClause(Literal l1, Literal l2, Literal l3)
{
  Literal ls[3] = {l1, l2, l3};
  mkGateClause(3, ls);
}

void PropCore::mkRootClause(size_t numLits, Literal* lits)
{
  mkClause(numLits, lits);
}

void PropCore::mkRootClause(Literal l1, Literal l2)
{
  Literal ls[2] = {l1, l2};
  mkRootClause(2, ls);
}

void PropCore::addAndRelWatches(TNode n)
{
  RelevancyHandler* eh = d_relevancyPropagator->mkAndRelevancyHandler(n);
  for (const Node& arg : n)
  {
    // if one child is assigned false, the and-parent must be notified
    addRelWatch(~getLiteral(arg), eh);
  }
}

void PropCore::addOrRelWatches(TNode n)
{
  RelevancyHandler* eh = d_relevancyPropagator->mkOrRelevancyHandler(n);
  for (const Node& arg : n)
  {
    // if one child is assigned true, the or-parent must be notified
    addRelWatch(getLiteral(arg), eh);
  }
}

void PropCore::addImpliesRelWatches(TNode n)
{
  RelevancyHandler* eh = d_relevancyPropagator->mkImpliesRelevancyHandler(n);
  addRelWatch(~getLiteral(n[0]), eh);
  addRelWatch(getLiteral(n[1]), eh);
}

void PropCore::addIteRelWatches(TNode n)
{
  RelevancyHandler* eh = d_relevancyPropagator->mkIteRelevancyHandler(n);
  Literal l = getLiteral(n[0]);
  // when the condition of an ite is assigned, the ite-parent is notified
  addRelWatch(l, eh);
  addRelWatch(~l, eh);
}

void PropCore::mkNotCnstr(TNode n)
{
  Assert(bInternalized(n));
  BoolVar v = getBoolVar(n);
  Literal l(v, false);
  Literal c = getLiteral(n[0]);
  mkGateClause(~l, ~c);
  mkGateClause(l, c);
}

void PropCore::mkAndCnstr(TNode n)
{
  Literal l = getLiteral(n);
  LiteralVector buffer;
  buffer.push_back(l);
  for (const Node& arg : n)
  {
    Literal lArg = getLiteral(arg);
    mkGateClause(~l, lArg);
    buffer.push_back(~lArg);
  }
  mkGateClause(buffer.size(), buffer.data());
}

void PropCore::mkOrCnstr(TNode n)
{
  Literal l = getLiteral(n);
  LiteralVector buffer;
  buffer.push_back(~l);
  for (const Node& arg : n)
  {
    Literal lArg = getLiteral(arg);
    mkGateClause(l, ~lArg);
    buffer.push_back(lArg);
  }
  mkGateClause(buffer.size(), buffer.data());
}

void PropCore::mkImpliesCnstr(TNode n)
{
  Literal l = getLiteral(n);
  LiteralVector buffer;
  buffer.push_back(~l);
  Literal lArg1 = getLiteral(n[0]);
  mkGateClause(l, lArg1);
  buffer.push_back(~lArg1);
  Literal lArg2 = getLiteral(n[1]);
  mkGateClause(l, ~lArg2);
  buffer.push_back(lArg2);
  mkGateClause(buffer.size(), buffer.data());
}

void PropCore::mkIffCnstr(TNode n, bool sign)
{
  if (n.getNumChildren() != 2)
  {
    Unreachable() << "z3: formula has not been simplified: " << n;
  }
  Literal l = getLiteral(n);
  Literal l1 = getLiteral(n[0]);
  Literal l2 = getLiteral(n[1]);
  if (sign)
  {
    l.neg();
  }
  mkGateClause(~l, l1, ~l2);
  mkGateClause(~l, ~l1, l2);
  mkGateClause(l, l1, l2);
  mkGateClause(l, ~l1, ~l2);
}

void PropCore::mkIteCnstr(TNode n)
{
  Literal l = getLiteral(n);
  Literal l1 = getLiteral(n[0]);
  Literal l2 = getLiteral(n[1]);
  Literal l3 = getLiteral(n[2]);
  mkGateClause(~l, ~l1, l2);
  mkGateClause(~l, l1, l3);
  mkGateClause(l, ~l1, ~l2);
  mkGateClause(l, l1, ~l3);
}

// ----------------------------------------------------------------- relevancy

void PropCore::notifyRelevant(TNode n)
{
  if (bInternalized(n))
  {
    BoolVar v = getBoolVar(n);
    BoolVarData& d = getBdata(v);
    // An assigned atom reaches the theory side once it is relevant.
    if (d.isAtom())
    {
      SatValue val = getAssignment(v);
      if (val != SAT_VALUE_UNKNOWN)
      {
        d_ctx.enqueueAtom(Literal(v, val == SAT_VALUE_FALSE));
      }
    }
    if (getAssignment(v) == SAT_VALUE_UNKNOWN)
    {
      d_hostRelevant.push_back(n);
    }
  }
  d_ctx.notifyRelevant(n);
}

void PropCore::propagateRelevancy(size_t qhead)
{
  size_t sz = d_assignedLiterals.size();
  while (qhead < sz)
  {
    Literal l = d_assignedLiterals[qhead];
    Assert(getAssignment(l) == SAT_VALUE_TRUE);
    qhead++;
    BoolVar var = l.var();
    TNode n = boolVar2Expr(var);
    d_relevancyPropagator->notifyAssigned(n, !l.sign());
  }
  d_relevancyPropagator->propagate();
}

// -------------------------------------------------------------------- scopes

void PropCore::pushScope()
{
  d_scopeLvl++;
  d_scopes.push_back(Scope{d_assignedLiterals.size(),
                           d_auxClauses.size(),
                           d_unitsToReassert.size()});
  d_ctx.pushTheoryScope();
}

void PropCore::popScope(size_t numScopes)
{
  Assert(numScopes > 0);
  Assert(numScopes <= d_scopeLvl);
  Assert(d_scopes.size() == d_scopeLvl);

  uint32_t newLvl = d_scopeLvl - static_cast<uint32_t>(numScopes);

  // The order is that of Z3's pop_scope_core, except that the theory side's
  // state other than the trail is popped in one step, after this side's
  // clauses and relevancy, which are independent of it.
  cacheGeneration(newLvl);
  Scope& sc = d_scopes[newLvl];
  d_conflict = false;
  delClauses(d_auxClauses, sc.d_auxClausesLim);
  size_t unitsToReassertLim = sc.d_unitsToReassertLim;
  d_ctx.popTheoryScopeBegin();
  unassignVars(d_scopes[newLvl].d_assignedLiteralsLim);
  d_ctx.popTheoryScopeEnd(numScopes);
  d_scopes.resize(newLvl);
  d_scopeLvl = newLvl;

  reassertUnits(unitsToReassertLim);
  d_ctx.resetCacheGeneration();
}

void PropCore::popToBaseLvl()
{
  if (!atBaseLevel())
  {
    popScope(d_scopeLvl);
  }
}

// ----------------------------------------------------------- the Boolean core

void PropCore::assignCore(Literal l)
{
  d_assignedLiterals.push_back(l);
  d_assignment[l.index()] = SAT_VALUE_TRUE;
  d_assignment[(~l).index()] = SAT_VALUE_FALSE;
  const BoolVarData& d = getBdata(l.var());
  d_stats.d_numAssignments++;
  if (d.isAtom() && isRelevantCore(boolVar2Expr(l.var())))
  {
    d_ctx.enqueueAtom(l);
  }
}

bool PropCore::bcp()
{
  Assert(!inconsistent());
  while (d_qhead < d_assignedLiterals.size())
  {
    if (d_ctx.getCancelFlag())
    {
      return true;
    }
    Literal l = d_assignedLiterals[d_qhead];
    Assert(getAssignment(l) == SAT_VALUE_TRUE);
    d_qhead++;
    Literal notL = ~l;
    Assert(getAssignment(notL) == SAT_VALUE_FALSE);
    WatchList& w = d_watches[l.index()];
    // binary clause propagation, the most recent watch first, as in Z3
    const std::vector<Literal>& lits = w.getLiterals();
    for (auto bit = lits.rbegin(), bend = lits.rend(); bit != bend; ++bit)
    {
      Literal l2 = *bit;
      switch (getAssignment(l2))
      {
        case SAT_VALUE_FALSE:
          d_stats.d_numBinPropagations++;
          setConflict();
          return false;
        case SAT_VALUE_UNKNOWN:
          d_stats.d_numBinPropagations++;
          assignCore(l2);
          break;
        case SAT_VALUE_TRUE: break;
      }
    }

    // non-binary clause propagation
    WatchList::ClauseIterator it = w.beginClause();
    WatchList::ClauseIterator it2 = it;
    WatchList::ClauseIterator end = w.endClause();
    for (; it != end; ++it)
    {
      Clause* cls = *it;
      Assert(cls->getLiteral(0) == notL || cls->getLiteral(1) == notL);
      if (cls->getLiteral(0) == notL)
      {
        cls->setLiteral(0, cls->getLiteral(1));
        cls->setLiteral(1, notL);
      }
      Assert(cls->getLiteral(1) == notL);

      Literal firstLit = cls->getLiteral(0);
      SatValue firstLitVal = getAssignment(firstLit);

      if (firstLitVal == SAT_VALUE_TRUE)
      {
        *it2 = *it;  // the clause is already satisfied, keep it
        it2++;
        continue;
      }
      Literal* it3 = cls->begin() + 2;
      Literal* end3 = cls->end();
      bool foundWatch = false;
      for (; it3 != end3; ++it3)
      {
        if (getAssignment(*it3) != SAT_VALUE_FALSE)
        {
          // Swap *it3 with the literal at position 1; the negation of *it3
          // will watch cls from now on.
          d_watches[(~(*it3)).index()].insertClause(cls);
          cls->setLiteral(1, *it3);
          *it3 = notL;
          foundWatch = true;
          break;
        }
      }
      if (foundWatch)
      {
        continue;
      }
      // did not find a watch
      if (firstLitVal == SAT_VALUE_FALSE)
      {
        // CONFLICT: copy the remaining watches
        while (it < end)
        {
          *it2 = *it;
          it2++;
          it++;
        }
        Assert(it2 <= end);
        w.setEndClause(it2);
        setConflict();
        return false;
      }
      // PROPAGATION
      Assert(firstLitVal == SAT_VALUE_UNKNOWN);
      *it2 = *it;
      it2++;  // keep the clause
      d_stats.d_numPropagations++;
      // It is safe to call assignCore instead of assign, since firstLit is
      // unassigned.
      assignCore(firstLit);
    }
    Assert(it2 <= end);
    w.setEndClause(it2);
  }
  return true;
}

SatValue PropCore::getAssignment(TNode n) const
{
  if (isFalseNode(n))
  {
    return SAT_VALUE_FALSE;
  }
  if (n.getKind() == Kind::NOT)
  {
    Assert(bInternalized(n[0]));
    return ~getAssignment(getBoolVarOfId(n[0].getId()));
  }
  Assert(bInternalized(n));
  BoolVar var = getBoolVarOfId(n.getId());
  Assert(var != s_nullBoolVar);
  return getAssignment(var);
}

SatValue PropCore::findAssignment(TNode n) const
{
  if (n.getKind() == Kind::NOT)
  {
    TNode arg = n[0];
    if (bInternalized(arg))
    {
      return ~getAssignment(getBoolVarOfId(arg.getId()));
    }
    if (isFalseNode(arg))
    {
      return SAT_VALUE_TRUE;
    }
    if (isTrueNode(arg))
    {
      return SAT_VALUE_FALSE;
    }
    return SAT_VALUE_UNKNOWN;
  }
  if (bInternalized(n))
  {
    return getAssignment(n);
  }
  if (isFalseNode(n))
  {
    return SAT_VALUE_FALSE;
  }
  if (isTrueNode(n))
  {
    return SAT_VALUE_TRUE;
  }
  return SAT_VALUE_UNKNOWN;
}

Literal PropCore::getLiteral(TNode n) const
{
  if (n.getKind() == Kind::NOT)
  {
    return ~getLiteral(n[0]);
  }
  if (isTrueNode(n))
  {
    return s_trueLiteral;
  }
  if (isFalseNode(n))
  {
    return s_falseLiteral;
  }
  Assert(bInternalized(n));
  return Literal(getBoolVar(n), false);
}

void PropCore::removeWatchLiteral(Clause* cls, size_t idx)
{
  d_watches[(~cls->getLiteral(idx)).index()].removeClause(cls);
}

void PropCore::delClause(Clause* cls)
{
  if (!cls->deleted())
  {
    removeWatchLiteral(cls, 0);
    removeWatchLiteral(cls, 1);
  }
  cls->deallocate();
  d_stats.d_numDelClause++;
}

void PropCore::delClauses(ClauseVector& v, size_t oldSize)
{
  size_t numCollect = v.size() - oldSize;
  if (numCollect == 0)
  {
    return;
  }

  if (numCollect > 1000)
  {
    // For a large batch it is cheaper to mark everything deleted first and
    // then sweep the affected watch lists once.
    std::vector<bool> watches(d_watches.size(), false);
    for (size_t i = v.size(); i != oldSize;)
    {
      --i;
      Clause* c = v[i];
      if (!c->deleted())
      {
        c->markAsDeleted();
      }
      watches[(~c->getLiteral(0)).index()] = true;
      watches[(~c->getLiteral(1)).index()] = true;
    }
    for (size_t w = 0, sz = d_watches.size(); w < sz; ++w)
    {
      if (watches[w])
      {
        d_watches[w].removeDeleted();
      }
    }
    for (size_t i = v.size(); i != oldSize;)
    {
      --i;
      v[i]->deallocate();
    }
    d_stats.d_numDelClause += (v.size() - oldSize);
  }
  else
  {
    for (size_t i = v.size(); i != oldSize;)
    {
      --i;
      delClause(v[i]);
    }
  }
  v.resize(oldSize);
}

void PropCore::unassignVars(size_t oldLim)
{
  Assert(oldLim <= d_assignedLiterals.size());

  size_t i = d_assignedLiterals.size();
  while (i != oldLim)
  {
    --i;
    Literal l = d_assignedLiterals[i];
    d_assignment[l.index()] = SAT_VALUE_UNKNOWN;
    d_assignment[(~l).index()] = SAT_VALUE_UNKNOWN;
  }

  d_assignedLiterals.resize(oldLim);
  d_qhead = oldLim;
}

void PropCore::cacheGeneration(uint32_t newScopeLvl)
{
  // When a unit is reasserted its enodes and literals may have to be
  // recreated. The generation number of a recreated enode must be the one it
  // had before, otherwise it would reset to 0 and defeat the matching-loop
  // heuristics that control quantifier instantiation.
  Scope& s = d_scopes[newScopeLvl];
  for (size_t i = s.d_unitsToReassertLim, sz = d_unitsToReassert.size(); i < sz;
       ++i)
  {
    d_ctx.cacheGeneration(d_unitsToReassert[i].d_unit, newScopeLvl);
  }
}

void PropCore::reassertUnits(size_t unitsToReassertLim)
{
  for (size_t i = unitsToReassertLim, sz = d_unitsToReassert.size(); i < sz;
       ++i)
  {
    ReplayUnit& ru = d_unitsToReassert[i];
    d_ctx.internalize(ru.d_unit, true);
    BoolVar v = getBoolVar(ru.d_unit);
    Assert(v != s_nullBoolVar) << "unit without a variable: " << ru.d_unit;
    Literal l(v, ru.d_sign);
    assign(l);
    if (ru.d_relevant)
    {
      markAsRelevant(l);
    }
  }
  if (atBaseLevel())
  {
    d_unitsToReassert.clear();
  }
}

BoolVar PropCore::mkBoolVar(TNode n)
{
  Assert(!bInternalized(n));
  size_t id = n.getId();
  BoolVar v = static_cast<BoolVar>(d_bInternalizedStack.size());
  setBoolVar(id, v);
  if (d_bdata.size() < v + 1)
  {
    d_bdata.resize(v + 1, BoolVarData());
  }
  if (d_boolVar2Expr.size() < v + 1)
  {
    d_boolVar2Expr.resize(v + 1, Node::null());
  }
  d_boolVar2Expr[v] = n;

  Literal l(v, false);
  Literal notL(v, true);
  size_t aux = std::max(l.index(), notL.index()) + 1;
  if (d_assignment.size() < aux)
  {
    d_assignment.resize(aux, SAT_VALUE_UNKNOWN);
  }
  d_assignment[l.index()] = SAT_VALUE_UNKNOWN;
  d_assignment[notL.index()] = SAT_VALUE_UNKNOWN;
  if (d_watches.size() < aux)
  {
    d_watches.resize(aux);
  }
  Assert(d_assignment.size() == d_watches.size());
  d_watches[l.index()].reset();
  d_watches[notL.index()].reset();
  // record the level at which the variable was internalized
  d_bdata[v].init(d_scopeLvl);
  d_bInternalizedStack.push_back(n);
  d_ctx.pushTrailPtr(&d_mkBoolVarTrail);
  d_stats.d_numMkBoolVar++;
  return v;
}

void PropCore::undoMkBoolVar()
{
  Assert(!d_bInternalizedStack.empty());
  d_stats.d_numDelBoolVar++;
  Node n = d_bInternalizedStack.back();
  size_t nId = n.getId();
  BoolVar v = getBoolVarOfId(nId);
  d_boolVar2Expr[v] = Node::null();
  d_ctx.notifyBoolVarDeleted(n);
  setBoolVar(nId, s_nullBoolVar);
  d_bInternalizedStack.pop_back();
}

bool PropCore::simplifyAuxClauseLiterals(size_t& numLits, Literal* lits)
{
  // Simplify the literals of a transient (auxiliary) clause using the current
  // assignment, which is safe because such clauses are deleted on
  // backtracking. Duplicates and false literals are removed; the clause is
  // reported as equivalent to true (by returning false) if it contains a true
  // literal or both l and ~l.
  std::sort(lits, lits + numLits);
  Literal prev = s_nullLiteral;
  size_t j = 0;
  for (size_t i = 0; i < numLits; ++i)
  {
    Literal curr = lits[i];
    switch (getAssignment(curr))
    {
      case SAT_VALUE_FALSE: prev = curr; break;  // ignore the literal
      case SAT_VALUE_UNKNOWN:
        if (curr == ~prev)
        {
          return false;  // the clause is equivalent to true
        }
        if (curr != prev)
        {
          prev = curr;
          if (i != j)
          {
            lits[j] = lits[i];
          }
          j++;
        }
        break;
      case SAT_VALUE_TRUE: return false;  // the clause is equivalent to true
    }
  }
  numLits = j;
  return true;
}

bool PropCore::useBinaryClauseOpt(Literal l1, Literal l2) const
{
  // A binary clause is kept only in the watch lists, which backtracking does
  // not undo, so only one made at the base level over variables of the base
  // level can be.
  if (d_scopeLvl > 0)
  {
    return false;
  }
  if (getInternLevel(l1.var()) > 0)
  {
    return false;
  }
  if (getInternLevel(l2.var()) > 0)
  {
    return false;
  }
  return true;
}

void PropCore::addWatchLiteral(Clause* cls, size_t idx)
{
  Assert(idx == 0 || idx == 1);
  Literal l = cls->getLiteral(idx);
  d_watches[(~l).index()].insertClause(cls);
}

Clause* PropCore::mkClause(size_t numLits, Literal* lits)
{
  if (!simplifyAuxClauseLiterals(numLits, lits))
  {
    return nullptr;  // the clause is equivalent to true
  }
  d_stats.d_numMkLits += numLits;

  switch (numLits)
  {
    case 0:
      setConflict();
      Assert(inconsistent());
      return nullptr;
    case 1: assign(lits[0]); return nullptr;
    case 2:
      if (useBinaryClauseOpt(lits[0], lits[1]))
      {
        Literal l1 = lits[0];
        Literal l2 = lits[1];
        d_watches[(~l1).index()].insertLiteral(l2);
        d_watches[(~l2).index()].insertLiteral(l1);
        if (getAssignment(l1) == SAT_VALUE_FALSE)
        {
          assign(l2);
        }
        else if (getAssignment(l2) == SAT_VALUE_FALSE)
        {
          assign(l1);
        }
        d_stats.d_numMkBinClause++;
        return nullptr;
      }
      CVC5_FALLTHROUGH;
    default:
    {
      d_stats.d_numMkClause++;
      Clause* cls = Clause::mk(numLits, lits);
      d_auxClauses.push_back(cls);
      addWatchLiteral(cls, 0);
      addWatchLiteral(cls, 1);
      if (getAssignment(cls->getLiteral(0)) == SAT_VALUE_FALSE)
      {
        setConflict();
      }
      else if (getAssignment(cls->getLiteral(1)) == SAT_VALUE_FALSE)
      {
        assign(cls->getLiteral(0));
      }
      return cls;
    }
  }
}

// ------------------------------------------------------------------ host mode

void PropCore::hostInit()
{
  d_stats.d_numAssertedFormulas =
      static_cast<int64_t>(d_assertedFormulas.size());
  popToBaseLvl();
  internalizeAssertions();
  d_ctx.initSearch();
  d_resourceOut = false;
  d_searching = true;
}

void PropCore::hostSyncLevel(uint32_t lvl)
{
  while (d_scopeLvl < lvl)
  {
    pushScope();
  }
  if (d_scopeLvl > lvl)
  {
    popScope(d_scopeLvl - lvl);
  }
}

Literal PropCore::hostLiteral(TNode n)
{
  bool neg = n.getKind() == Kind::NOT;
  TNode atom = neg ? n[0] : n;
  if (!bInternalized(atom))
  {
    d_ctx.internalize(atom, true);
  }
  Literal l = getLiteral(atom);
  return neg ? ~l : l;
}

bool PropCore::hostAssign(Literal l)
{
  switch (getAssignment(l))
  {
    // this side derived l before the host asserted it
    case SAT_VALUE_TRUE: return true;
    case SAT_VALUE_UNKNOWN: assign(l); return true;
    // this side derived ~l, which the host contradicts
    case SAT_VALUE_FALSE: return false;
  }
  return true;
}

bool PropCore::hostFinalCheck() { return d_ctx.finalCheck(); }

}  // namespace z3
}  // namespace cvc5::internal
