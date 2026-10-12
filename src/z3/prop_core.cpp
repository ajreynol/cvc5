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

#include "z3/prop_core.h"

#include <algorithm>

#include "base/output.h"
#include "expr/node_manager.h"
#include "z3/smt_context.h"
#include "z3/theory.h"
#include "z3/util/uint_set.h"

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

}  // namespace

PropCore::PropCore(Env& env, SmtContext& ctx, Params& params, Statistics& stats)
    : EnvObj(env),
      d_ctx(ctx),
      d_params(params),
      d_stats(stats),
      d_qhead(0),
      d_simpQhead(0),
      d_simpCounter(0),
      d_caseSplitQueue(nullptr),
      d_bvarInc(1.0),
      d_phaseCacheOn(true),
      d_phaseCounter(0),
      d_phaseDefault(false),
      d_agility(0.0),
      d_conflict(s_nullBJustification),
      d_notL(s_nullLiteral),
      d_assertedInconsistent(false),
      d_flushing(false),
      d_scopeLvl(0),
      d_baseLvl(0),
      d_searchLvl(0),
      d_mkBoolVarTrail(*this)
{
}

PropCore::~PropCore() {}

void PropCore::finishInit()
{
  d_caseSplitQueue.reset(mkCaseSplitQueue(d_ctx, d_params));
}

void PropCore::initTrue(TNode t)
{
  mkBoolVar(t);
  Assert(getBoolVar(t) == s_trueBoolVar);
  Assert(s_trueLiteral.var() == s_trueBoolVar);
  d_assignment[s_trueLiteral.index()] = L_TRUE;
  d_assignment[s_falseLiteral.index()] = L_FALSE;
  d_bdata[s_trueBoolVar].setAxiom();
}

void PropCore::flushClauses()
{
  d_flushing = true;
  delClauses(d_auxClauses, 0);
  delClauses(d_lemmas, 0);
  d_flushing = false;
}

void PropCore::initSearch()
{
  d_agility = 0.0;
  d_phaseDefault = false;
  d_caseSplitQueue->initSearchEh();
}

void PropCore::endSearch() { d_caseSplitQueue->endSearchEh(); }

void PropCore::pushScope()
{
  d_scopeLvl++;
  d_scopes.push_back(Scope{d_assignedLiterals.size(),
                           d_auxClauses.size(),
                           d_unitsToReassert.size()});
}

void PropCore::pushBaseScope()
{
  d_baseScopes.push_back(
      BaseScope{d_lemmas.size(), d_simpQhead, inconsistent()});
  d_baseLvl++;
  // Not really necessary, but it keeps the invariant d_searchLvl >= d_baseLvl.
  d_searchLvl++;
  Assert(d_baseLvl <= d_scopeLvl);
}

size_t PropCore::popClauses(uint32_t newLvl)
{
  Scope& s = d_scopes[newLvl];
  if (newLvl < d_baseLvl)
  {
    BaseScope& bs = d_baseScopes[newLvl];
    delClauses(d_lemmas, bs.d_lemmasLim);
    d_simpQhead = bs.d_simpQheadLim;
    if (!bs.d_inconsistent)
    {
      d_conflict = s_nullBJustification;
      d_notL = s_nullLiteral;
    }
    d_baseScopes.resize(newLvl);
  }
  else
  {
    d_conflict = s_nullBJustification;
    d_notL = s_nullLiteral;
  }
  delClauses(d_auxClauses, s.d_auxClausesLim);
  return s.d_unitsToReassertLim;
}

void PropCore::unassignToScope(uint32_t newLvl)
{
  unassignVars(d_scopes[newLvl].d_assignedLiteralsLim);
}

void PropCore::popScopeLevels(uint32_t newLvl)
{
  d_scopes.resize(newLvl);
  d_scopeLvl = newLvl;
  if (newLvl < d_baseLvl)
  {
    d_baseLvl = newLvl;
    // not strictly necessary
    d_searchLvl = newLvl;
  }
}

void PropCore::delInactiveLemmas()
{
  if (d_params.d_lemmaGcHalf)
  {
    delInactiveLemmas1();
  }
  else
  {
    delInactiveLemmas2();
  }
}

void PropCore::setJustification(BoolVar /*v*/,
                                BoolVarData& d,
                                const BJustification& j)
{
  d.setJustification(j);
}

void PropCore::assignCore(Literal l, BJustification j, bool decision)
{
  d_assignedLiterals.push_back(l);
  d_assignment[l.index()] = L_TRUE;
  d_assignment[(~l).index()] = L_FALSE;
  BoolVarData& d = getBdata(l.var());
  setJustification(l.var(), d, j);
  d.d_scopeLvl = d_scopeLvl;
  if (d_params.d_restartAdaptive && d.d_phaseAvailable)
  {
    d_agility *= d_params.d_agilityFactor;
    if (!decision && d.d_phase == l.sign())
    {
      d_agility += (1.0 - d_params.d_agilityFactor);
    }
  }
  bool newPhase = !l.sign();
  d_stats.d_numAssignments++;
  if (d.d_phaseAvailable && d.d_phase != newPhase)
  {
    // reset the birthdate when the phase changes
    d_birthdate[l.var()] = d_stats.d_numAssignments;
  }
  d.d_phaseAvailable = true;
  d.d_phase = newPhase;

  if (d.isAtom()
      && (d_ctx.relevancyLvl() == 0
          || (d_ctx.relevancyLvl() == 1 && !d.isQuantifier())
          || d_ctx.isRelevantCore(l)))
  {
    d_ctx.enqueueAtom(l);
  }

  d_caseSplitQueue->assignLitEh(l);
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
    Assert(getAssignment(l) == L_TRUE);
    d_qhead++;
    d_simpCounter--;
    Literal notL = ~l;
    Assert(getAssignment(notL) == L_FALSE);
    WatchList& w = d_watches[l.index()];
    if (binaryClauseOptEnabled())
    {
      // binary clause propagation
      BJustification js(l);
      Literal* it = w.beginLiterals();
      Literal* end = w.endLiterals();
      for (; it != end; ++it)
      {
        Literal l2 = *it;
        switch (getAssignment(l2))
        {
          case L_FALSE:
            d_stats.d_numBinPropagations++;
            setConflict(js, ~l2);
            return false;
          case L_UNDEF:
            d_stats.d_numBinPropagations++;
            assignCore(l2, js);
            break;
          case L_TRUE: break;
        }
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
      LBool firstLitVal = getAssignment(firstLit);

      if (firstLitVal == L_TRUE)
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
        if (getAssignment(*it3) != L_FALSE)
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
      if (firstLitVal == L_FALSE)
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
        Assert(isEmptyClause(cls));
        setConflict(BJustification(cls));
        return false;
      }
      // PROPAGATION
      Assert(firstLitVal == L_UNDEF);
      Assert(isUnitClause(cls));
      *it2 = *it;
      it2++;  // keep the clause
      d_stats.d_numPropagations++;
      // It is safe to call assignCore instead of assign, since firstLit is
      // unassigned.
      assignCore(firstLit, BJustification(cls));
      if (d_params.d_relevancyLemma && cls->isLemma())
      {
        d_ctx.markAsRelevant(boolVar2Expr(firstLit.var()));
      }
    }
    Assert(it2 <= end);
    w.setEndClause(it2);
  }
  return true;
}

LBool PropCore::getAssignment(TNode n) const
{
  if (isFalseNode(n))
  {
    return L_FALSE;
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

LBool PropCore::findAssignment(TNode n) const
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
      return L_TRUE;
    }
    if (isTrueNode(arg))
    {
      return L_FALSE;
    }
    return L_UNDEF;
  }
  if (bInternalized(n))
  {
    return getAssignment(n);
  }
  if (isFalseNode(n))
  {
    return L_FALSE;
  }
  if (isTrueNode(n))
  {
    return L_TRUE;
  }
  return L_UNDEF;
}

Node PropCore::literal2Expr(Literal l) const
{
  if (l == s_trueLiteral)
  {
    return nodeManager()->mkConst(true);
  }
  if (l == s_falseLiteral)
  {
    return nodeManager()->mkConst(false);
  }
  if (l.sign())
  {
    return nodeManager()->mkNode(Kind::NOT, boolVar2Expr(l.var()));
  }
  return boolVar2Expr(l.var());
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

void PropCore::setConflict(const BJustification& js, Literal notL)
{
  if (d_conflict == s_nullBJustification)
  {
    d_conflict = js;
    d_notL = notL;
  }
}

void PropCore::rescaleBoolVarActivity()
{
  for (double& a : d_activity)
  {
    a *= s_invActivityLimit;
  }
  d_bvarInc *= s_invActivityLimit;
}

bool PropCore::guess(BoolVar var, LBool phase)
{
  if (isQuantifier(d_boolVar2Expr[var]))
  {
    // Override any decision about how to assign the quantifier: assigning a
    // quantifier to false is the same as making it irrelevant.
    phase = L_FALSE;
  }
  Literal l(var, false);

  if (phase != L_UNDEF)
  {
    return phase == L_TRUE;
  }

  BoolVarData& d = d_bdata[var];
  if (d.tryTrueFirst())
  {
    return true;
  }
  switch (d_params.d_phaseSelection)
  {
    case PS_THEORY:
      if (d_phaseCacheOn && d.d_phaseAvailable)
      {
        return d_bdata[var].d_phase;
      }
      if (!d_phaseCacheOn && d.isTheoryAtom())
      {
        Theory* th = d_ctx.getTheory(d.getTheory());
        LBool thPhase = th->getPhase(var);
        if (thPhase != L_UNDEF)
        {
          return thPhase == L_TRUE;
        }
      }
      if (trackOccs())
      {
        if (d_litOccs[l.index()] == 0)
        {
          return false;
        }
        if (d_litOccs[(~l).index()] == 0)
        {
          return true;
        }
      }
      return d_phaseDefault;
    case PS_CACHING:
    case PS_CACHING_CONSERVATIVE:
    case PS_CACHING_CONSERVATIVE2:
      if (d_phaseCacheOn && d.d_phaseAvailable)
      {
        Trace("z3-events") << "PHASESEL cached " << d_bdata[var].d_phase
                           << std::endl;
        return d_bdata[var].d_phase;
      }
      Trace("z3-events") << "PHASESEL default cacheOn " << d_phaseCacheOn
                         << " available " << d.d_phaseAvailable << std::endl;
      return d_phaseDefault;
    case PS_ALWAYS_FALSE: return false;
    case PS_ALWAYS_TRUE: return true;
    case PS_RANDOM: return d_ctx.getRandomValue() % 2 == 0;
    case PS_OCCURRENCE: return d_litOccs[l.index()] > d_litOccs[(~l).index()];
  }
  Unreachable();
  return false;
}

void PropCore::updatePhaseCacheCounter()
{
  d_phaseCounter++;
  if (d_phaseCacheOn)
  {
    if (d_phaseCounter >= d_params.d_phaseCachingOn)
    {
      d_phaseCounter = 0;
      d_phaseCacheOn = false;
      if (d_params.d_phaseSelection == PS_CACHING_CONSERVATIVE2)
      {
        d_phaseDefault = !d_phaseDefault;
      }
    }
  }
  else
  {
    if (d_phaseCounter >= d_params.d_phaseCachingOff)
    {
      d_phaseCounter = 0;
      d_phaseCacheOn = true;
      if (d_params.d_phaseSelection == PS_CACHING_CONSERVATIVE2)
      {
        d_phaseDefault = !d_phaseDefault;
      }
    }
  }
}

void PropCore::removeWatchLiteral(Clause* cls, size_t idx)
{
  d_watches[(~cls->getLiteral(idx)).index()].removeClause(cls);
}

void PropCore::removeWatch(BoolVar v)
{
  Literal lit(v);
  d_watches[lit.index()].reset();
  d_watches[(~lit).index()].reset();
}

void PropCore::removeClsOccs(Clause* cls)
{
  removeWatchLiteral(cls, 0);
  removeWatchLiteral(cls, 1);
  removeLitOccs(*cls, getNumBoolVars());
}

void PropCore::addLitOccs(const Clause& cls)
{
  if (!trackOccs())
  {
    return;
  }
  for (Literal l : cls)
  {
    incRef(l);
  }
}

void PropCore::removeLitOccs(const Clause& cls, size_t nbv)
{
  if (!trackOccs())
  {
    return;
  }
  for (Literal l : cls)
  {
    if (l.var() < nbv)
    {
      decRef(l);
    }
  }
}

void PropCore::decRef(Literal l)
{
  if (trackOccs() && d_litOccs[l.index()] > 0)
  {
    d_litOccs[l.index()]--;
  }
}

void PropCore::incRef(Literal l)
{
  if (trackOccs())
  {
    d_litOccs[l.index()]++;
  }
}

void PropCore::delClause(Clause* cls)
{
  Assert(d_flushing || !cls->inReinitStack());
  if (!cls->deleted())
  {
    removeClsOccs(cls);
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
    UIntSet watches;
    for (size_t i = v.size(); i != oldSize;)
    {
      --i;
      Clause* c = v[i];
      removeLitOccs(*c, getNumBoolVars());
      if (!c->deleted())
      {
        c->markAsDeleted();
      }
      watches.insert((~c->getLiteral(0)).index());
      watches.insert((~c->getLiteral(1)).index());
    }
    for (size_t w = 0, sz = d_watches.size(); w < sz; ++w)
    {
      if (watches.contains(w))
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
    d_assignment[l.index()] = L_UNDEF;
    d_assignment[(~l).index()] = L_UNDEF;
    BoolVar v = l.var();
    BoolVarData& d = getBdata(v);
    d.setNullJustification();
    d_caseSplitQueue->unassignVarEh(v);
  }

  d_assignedLiterals.resize(oldLim);
  d_qhead = oldLim;
}

bool PropCore::isEmptyClause(const Clause* c) const
{
  size_t numLits = c->getNumLiterals();
  for (size_t i = 0; i < numLits; ++i)
  {
    if (getAssignment(c->getLiteral(i)) != L_FALSE)
    {
      return false;
    }
  }
  return true;
}

bool PropCore::isUnitClause(const Clause* c) const
{
  bool found = false;
  size_t numLits = c->getNumLiterals();
  for (size_t i = 0; i < numLits; ++i)
  {
    switch (getAssignment(c->getLiteral(i)))
    {
      case L_FALSE: break;  // skip
      case L_UNDEF:
        if (found)
        {
          return false;
        }
        found = true;
        break;
      case L_TRUE: return false;  // the clause is already satisfied
    }
  }
  return found;
}

void PropCore::cacheGeneration(uint32_t newScopeLvl)
{
  // When a clause is reinitialized its enodes and literals may have to be
  // recreated. The generation number of a recreated enode must be the one it
  // had before, otherwise it would reset to 0 and defeat the matching-loop
  // heuristics that control quantifier instantiation.
  if (!d_clausesToReinit.empty())
  {
    size_t lim = d_scopeLvl;
    if (d_clausesToReinit.size() <= lim)
    {
      Assert(!d_clausesToReinit.empty());
      lim = d_clausesToReinit.size() - 1;
    }
    for (size_t i = newScopeLvl; i <= lim; ++i)
    {
      for (Clause* cls : d_clausesToReinit[i])
      {
        cacheGeneration(cls, newScopeLvl);
      }
    }
  }
  if (!d_unitsToReassert.empty())
  {
    Scope& s = d_scopes[newScopeLvl];
    for (size_t i = s.d_unitsToReassertLim, sz = d_unitsToReassert.size();
         i < sz;
         ++i)
    {
      d_ctx.cacheGeneration(d_unitsToReassert[i].d_unit, newScopeLvl);
    }
  }
}

void PropCore::cacheGeneration(const Clause* cls, uint32_t newScopeLvl)
{
  cacheGeneration(cls->getNumLiterals(), cls->begin(), newScopeLvl);
}

void PropCore::cacheGeneration(size_t numLits,
                               const Literal* lits,
                               uint32_t newScopeLvl)
{
  for (size_t i = 0; i < numLits; ++i)
  {
    BoolVar v = lits[i].var();
    uint32_t ilvl = getInternLevel(v);
    if (ilvl > newScopeLvl)
    {
      d_ctx.cacheGeneration(boolVar2Expr(v), newScopeLvl);
    }
  }
}

void PropCore::reinitClauses(size_t numScopes, size_t numBoolVars)
{
  // Reinitialize the lemmas that contain Boolean variables deleted during
  // backtracking. A clause has a dead variable if it contains a literal l
  // with l.var() >= numBoolVars.
  if (d_clausesToReinit.empty())
  {
    return;
  }
  size_t lim = d_scopeLvl + numScopes;
  if (d_clausesToReinit.size() <= lim)
  {
    Assert(!d_clausesToReinit.empty());
    lim = d_clausesToReinit.size() - 1;
  }
  for (size_t i = d_scopeLvl + 1; i <= lim; ++i)
  {
    ClauseVector& v = d_clausesToReinit[i];
    for (Clause* cls : v)
    {
      if (cls->deleted())
      {
        cls->releaseAtoms();
        cls->d_reinit = false;
        cls->d_reinternalizeAtoms = false;
        continue;
      }
      Assert(cls->inReinitStack());
      bool keep = false;
      if (cls->reinternalizeAtoms())
      {
        Assert(cls->getNumAtoms() == cls->getNumLiterals());
        for (size_t j = 0; j < 2; ++j)
        {
          Literal l = cls->getLiteral(j);
          if (l.var() < numBoolVars)
          {
            // This variable survived backtracking, so it still watches the
            // clause. Remove the watch, since the clause may end up with
            // different watch literals after reinitialization.
            removeWatchLiteral(cls, j);
          }
        }

        size_t num = cls->getNumLiterals();

        removeLitOccs(*cls, numBoolVars);

        for (size_t j = 0; j < num; ++j)
        {
          TNode atom = cls->getAtom(j);
          bool sign = cls->getAtomSign(j);
          // The atom can be a negation, which happens when the NOT occurs
          // under an uninterpreted function. Reinternalizing a NOT atom
          // requires gateCtx to be false, so that it really is
          // reinternalized.
          bool gateCtx = atom.getKind() != Kind::NOT;
          d_ctx.internalize(atom, gateCtx);
          Assert(bInternalized(atom));
          Literal l(getBoolVar(atom), sign);
          cls->setLiteral(j, l);
          if (cls->getKind() == CLS_TH_LEMMA)
          {
            d_ctx.markAsRelevant(l);
          }
        }
        int w1Idx = selectWatchLit(cls, 0);
        cls->swapLits(0, w1Idx);
        int w2Idx = selectWatchLit(cls, 1);
        cls->swapLits(1, w2Idx);
        addWatchLiteral(cls, 0);
        addWatchLiteral(cls, 1);

        addLitOccs(*cls);

        Literal l1 = cls->getLiteral(0);
        Literal l2 = cls->getLiteral(1);

        if (getAssignment(l1) == L_FALSE)
        {
          setConflict(BJustification(cls));
        }
        else if (getAssignment(l2) == L_FALSE)
        {
          assign(l1, BJustification(cls));
        }
        keep = true;
      }
      else
      {
        Literal l1 = cls->getLiteral(0);
        Literal l2 = cls->getLiteral(1);
        if (cls->getKind() == CLS_TH_LEMMA)
        {
          d_ctx.markAsRelevant(l1);
          d_ctx.markAsRelevant(l2);
        }
        if (getAssignment(l1) == L_FALSE && isEmptyClause(cls))
        {
          setConflict(BJustification(cls));
          keep = true;
        }
        else if (getAssignment(l2) == L_FALSE && getAssignment(l1) == L_UNDEF
                 && isUnitClause(cls))
        {
          assign(l1, BJustification(cls));
          keep = true;
        }
      }

      if (keep && d_scopeLvl > d_baseLvl)
      {
        d_clausesToReinit[d_scopeLvl].push_back(cls);
      }
      else
      {
        // The clause no longer needs to be in the reinit stack, because it
        // will be deleted when the base level is backtracked.
        cls->releaseAtoms();
        cls->d_reinit = false;
        cls->d_reinternalizeAtoms = false;
      }
    }
    v.clear();
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
    Literal l(v, ru.d_sign);
    assign(l, BJustification::mkAxiom());
    if (ru.d_relevant)
    {
      d_ctx.markAsRelevant(l);
    }
  }
  if (atBaseLevel())
  {
    d_unitsToReassert.clear();
  }
}

bool PropCore::simplifyClause(Clause& cls)
{
  // Simplify the clause using the current assignment, returning true if it is
  // already satisfied. Only safe at the base level, which is also why it is
  // safe for auxiliary clauses: they are deleted on backtracking.
  Assert(d_scopeLvl == d_baseLvl);
  size_t s = cls.getNumLiterals();
  if (getAssignment(cls[0]) == L_TRUE || getAssignment(cls[1]) == L_TRUE)
  {
    return true;
  }

  size_t i = 2;
  size_t j = i;
  bool isTaut = false;
  for (; i < s; ++i)
  {
    Literal l = cls[i];
    switch (getAssignment(l))
    {
      case L_FALSE: decRef(l); break;
      case L_TRUE: isTaut = true; CVC5_FALLTHROUGH;
      case L_UNDEF:
        if (i != j)
        {
          cls.swapLits(i, j);
        }
        j++;
        break;
    }
  }

  if (j < s)
  {
    cls.setNumLiterals(j);
    Assert(j >= 2);
  }

  return isTaut;
}

size_t PropCore::simplifyClauses(ClauseVector& clauses, size_t startingAt)
{
  size_t numDelClauses = 0;
  size_t j = startingAt;
  for (size_t i = startingAt, sz = clauses.size(); i < sz; ++i)
  {
    Clause* cls = clauses[i];
    Assert(!cls->inReinitStack());

    if (cls->deleted())
    {
      delClause(cls);
      numDelClauses++;
    }
    else if (simplifyClause(*cls))
    {
      for (size_t idx = 0; idx < 2; ++idx)
      {
        Literal l0 = (*cls)[idx];
        BJustification l0Js = getJustification(l0.var());
        if (l0Js != s_nullBJustification
            && l0Js.getKind() == BJustification::CLAUSE
            && l0Js.getClause() == cls)
        {
          // cls is the explanation of l0; since we are at the base level it
          // is safe to replace it with an axiom.
          Assert(d_scopeLvl == d_baseLvl);
          d_bdata[l0.var()].setAxiom();
        }
      }
      delClause(cls);
      numDelClauses++;
    }
    else
    {
      clauses[j] = cls;
      ++j;
      d_simpCounter += static_cast<int64_t>(cls->getNumLiterals());
    }
  }
  clauses.resize(j);
  return numDelClauses;
}

void PropCore::simplifyClauses()
{
  // Note that when assumptions are used, d_scopeLvl >= d_searchLvl >
  // d_baseLvl, so no simplification is performed.
  if (d_scopeLvl > d_baseLvl)
  {
    return;
  }

  size_t sz = d_assignedLiterals.size();
  Assert(d_simpQhead <= sz);

  if (d_simpQhead == sz || d_simpCounter > 0)
  {
    return;
  }

  if (d_auxClauses.empty() && d_lemmas.empty())
  {
    return;
  }

  // d_simpCounter balances the cost of simplifyClause: after this runs it
  // approximates the number of literals the next run would have to visit, and
  // it is decremented once per variable visited during propagation.
  d_simpCounter = 0;
  // d_simpQhead detects whether there are new literals assigned at the base
  // level.
  d_simpQhead = d_assignedLiterals.size();

  size_t numDelClauses = 0;

  Assert(d_scopeLvl == d_baseLvl);
  if (d_baseLvl == 0)
  {
    numDelClauses += simplifyClauses(d_auxClauses, 0);
    numDelClauses += simplifyClauses(d_lemmas, 0);
  }
  else
  {
    Scope& s = d_scopes[d_baseLvl - 1];
    BaseScope& bs = d_baseScopes[d_baseLvl - 1];
    numDelClauses += simplifyClauses(d_auxClauses, s.d_auxClausesLim);
    numDelClauses += simplifyClauses(d_lemmas, bs.d_lemmasLim);
  }
  d_stats.d_numDelClauses += numDelClauses;
  d_stats.d_numSimplifications++;
}

namespace {

struct ClauseLt
{
  bool operator()(Clause* cls1, Clause* cls2) const
  {
    return cls1->getActivity() > cls2->getActivity();
  }
};

}  // namespace

void PropCore::delInactiveLemmas1()
{
  // Delete (approximately) half of the low activity lemmas.
  size_t sz = d_lemmas.size();
  size_t startAt = d_baseLvl == 0 ? 0 : d_baseScopes[d_baseLvl - 1].d_lemmasLim;
  Assert(startAt <= sz);
  if (startAt + d_params.d_recentLemmasSize >= sz)
  {
    return;
  }
  size_t endAt = sz - d_params.d_recentLemmasSize;
  Assert(startAt < endAt);
  std::stable_sort(
      d_lemmas.begin() + startAt, d_lemmas.begin() + endAt, ClauseLt());
  size_t startDelAt = (startAt + endAt) / 2;
  size_t i = startDelAt;
  size_t j = i;
  for (; i < endAt; ++i)
  {
    Clause* cls = d_lemmas[i];
    if (canDelete(cls))
    {
      delClause(cls);
    }
    else
    {
      d_lemmas[j] = cls;
      j++;
    }
  }
  // keep the recent clauses
  for (; i < sz; ++i)
  {
    Clause* cls = d_lemmas[i];
    if (cls->deleted() && canDelete(cls))
    {
      delClause(cls);
    }
    else
    {
      d_lemmas[j++] = cls;
    }
  }
  d_lemmas.resize(j);
  if (d_params.d_clauseDecay > 1)
  {
    // rescale the activity
    for (i = startAt; i < j; ++i)
    {
      Clause* cls = d_lemmas[i];
      cls->setActivity(cls->getActivity() / d_params.d_clauseDecay);
    }
  }
}

void PropCore::delInactiveLemmas2()
{
  // A more selective version of delInactiveLemmas1: the lemmas are split into
  // an old and a new group by d_newOldRatio, and a clause is kept based on
  // its activity and its relevancy, with the thresholds depending on which
  // group it is in. A clause with many unassigned literals counts as less
  // relevant.
  size_t sz = d_lemmas.size();
  size_t startAt = d_baseLvl == 0 ? 0 : d_baseScopes[d_baseLvl - 1].d_lemmasLim;
  Assert(startAt <= sz);
  size_t realSz = sz - startAt;
  if (realSz == 0)
  {
    return;
  }
  // the index of the first lemma considered "new"
  size_t newFirstIdx =
      startAt
      + (realSz / d_params.d_newOldRatio) * (d_params.d_newOldRatio - 1);
  Assert(newFirstIdx <= sz);
  size_t i = startAt;
  size_t j = i;
  for (; i < sz; ++i)
  {
    Clause* cls = d_lemmas[i];
    if (canDelete(cls))
    {
      if (cls->deleted())
      {
        delClause(cls);
        continue;
      }
      uint32_t actThreshold =
          d_params.d_oldClauseActivity
          - (d_params.d_oldClauseActivity - d_params.d_newClauseActivity)
                * static_cast<uint32_t>((i - startAt) / realSz);
      if (cls->getActivity() < actThreshold)
      {
        uint32_t relThreshold = (i >= newFirstIdx)
                                    ? d_params.d_newClauseRelevancy
                                    : d_params.d_oldClauseRelevancy;
        if (moreThanKUnassignedLiterals(cls, relThreshold))
        {
          delClause(cls);
          continue;
        }
      }
    }
    d_lemmas[j] = cls;
    j++;
    cls->setActivity(
        static_cast<uint32_t>(cls->getActivity() / d_params.d_invClauseDecay));
  }
  Assert(j <= sz);
  d_lemmas.resize(j);
}

bool PropCore::moreThanKUnassignedLiterals(Clause* cls, size_t k)
{
  Assert(k > 0);
  for (Literal l : *cls)
  {
    if (getAssignment(l) == L_UNDEF)
    {
      k--;
      if (k == 0)
      {
        return true;
      }
    }
  }
  return false;
}

void PropCore::forgetPhaseOfVarsInCurrentLevel()
{
  size_t head =
      d_scopeLvl == 0 ? 0 : d_scopes[d_scopeLvl - 1].d_assignedLiteralsLim;
  size_t sz = d_assignedLiterals.size();
  for (size_t i = head; i < sz; ++i)
  {
    d_bdata[d_assignedLiterals[i].var()].d_phaseAvailable = false;
  }
}

namespace {

/** Undoes setTrueFirstFlag. */
class SetTrueFirstTrail : public Trail
{
 public:
  SetTrueFirstTrail(PropCore& core, BoolVar v) : d_core(core), d_var(v) {}
  void undo() override { d_core.getBdata(d_var).resetTrueFirstFlag(); }

 private:
  PropCore& d_core;
  BoolVar d_var;
};

}  // namespace

void PropCore::setTrueFirstFlag(BoolVar v)
{
  d_ctx.pushTrail(SetTrueFirstTrail(*this, v));
  d_bdata[v].setTrueFirstFlag();
}

BoolVar PropCore::mkBoolVar(TNode n)
{
  Assert(!bInternalized(n));
  size_t id = n.getId();
  BoolVar v = static_cast<BoolVar>(d_bInternalizedStack.size());
  setBoolVar(id, v);
  reservex(d_bdata, v + 1, BoolVarData());
  reservex(d_activity, v + 1, 0.0);
  reservex(d_boolVar2Expr, v + 1, Node::null());
  d_boolVar2Expr[v] = n;
  reservex(d_litScores[0], v + 1, 0.0);
  reservex(d_litScores[1], v + 1, 0.0);
  d_litScores[0][v] = 0.0;
  d_litScores[1][v] = 0.0;
  reservex(d_birthdate, v + 1, static_cast<uint64_t>(0));
  d_birthdate[v] = 0;

  Literal l(v, false);
  Literal notL(v, true);
  size_t aux = std::max(l.index(), notL.index()) + 1;
  reservex(d_assignment, aux, static_cast<int8_t>(L_UNDEF));
  d_assignment[l.index()] = L_UNDEF;
  d_assignment[notL.index()] = L_UNDEF;
  if (d_watches.size() < aux)
  {
    d_watches.resize(aux);
  }
  Assert(d_assignment.size() == d_watches.size());
  d_watches[l.index()].reset();
  d_watches[notL.index()].reset();
  reservex(d_litOccs, aux, static_cast<uint32_t>(0));
  d_litOccs[l.index()] = 0;
  d_litOccs[notL.index()] = 0;
  BoolVarData& data = d_bdata[v];
  // record the level at which the variable was internalized
  data.init(d_scopeLvl);
  if (d_params.d_randomInitialActivity == IA_RANDOM
      || (d_params.d_randomInitialActivity == IA_RANDOM_WHEN_SEARCHING
          && d_ctx.isSearching()))
  {
    d_activity[v] = -((d_ctx.getRandomValue() % 1000) / 1000.0);
  }
  else
  {
    d_activity[v] = 0.0;
  }
  d_caseSplitQueue->mkVarEh(v);
  d_bInternalizedStack.push_back(n);
  d_ctx.pushTrailPtr(&d_mkBoolVarTrail);
  d_stats.d_numMkBoolVar++;
  return v;
}

void PropCore::addScores(size_t n, const Literal* lits)
{
  for (size_t i = 0; i < n; ++i)
  {
    Literal lit = lits[i];
    d_litScores[lit.sign() ? 1 : 0][lit.var()] += 1.0 / n;
  }
}

void PropCore::undoMkBoolVar()
{
  Assert(!d_bInternalizedStack.empty());
  d_stats.d_numDelBoolVar++;
  Node n = d_bInternalizedStack.back();
  size_t nId = n.getId();
  BoolVar v = getBoolVarOfId(nId);
  d_boolVar2Expr[v] = Node::null();
  d_caseSplitQueue->delVarEh(v);
  d_ctx.notifyBoolVarDeleted(n);
  setBoolVar(nId, s_nullBoolVar);
  d_bInternalizedStack.pop_back();
}

bool PropCore::simplifyAuxClauseLiterals(size_t& numLits,
                                         Literal* lits,
                                         LiteralVector& simpLits)
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
      case L_FALSE:
        if (curr != prev)
        {
          prev = curr;
          simpLits.push_back(~curr);
        }
        break;  // ignore the literal
      case L_UNDEF:
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
      case L_TRUE: return false;  // the clause is equivalent to true
    }
  }
  numLits = j;
  return true;
}

bool PropCore::simplifyAuxLemmaLiterals(size_t& numLits, Literal* lits)
{
  // An auxiliary lemma has the status of a learned clause but was not
  // produced by conflict resolution; a dynamic Ackermann clause is one
  // example. Literals assigned false at the base level are *not* removed,
  // because that would need a justification for the simplification.
  std::sort(lits, lits + numLits);
  Literal prev = s_nullLiteral;
  size_t i = 0;
  size_t j = 0;
  for (; i < numLits; ++i)
  {
    Literal curr = lits[i];
    BoolVar var = curr.var();
    LBool val = L_UNDEF;
    if (getAssignLevel(var) <= d_baseLvl)
    {
      val = getAssignment(curr);
    }
    if (val == L_TRUE)
    {
      return false;  // the clause is equivalent to true
    }
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
  }
  numLits = j;
  return true;
}

void PropCore::markForReinit(Clause* cls,
                             uint32_t scopeLvl,
                             bool reinternalizeAtoms)
{
  // A clause may need reinitialization for two reasons. First, it may contain
  // literals created during the search, whose maximum internalization level
  // is scopeLvl; since the clause can outlive that level it has to be rebuilt
  // (reinternalizeAtoms is true in that case). Second, an auxiliary lemma may
  // have been in conflict or propagating when it was created, which has to be
  // rechecked after backtracking.
  Assert(scopeLvl >= d_baseLvl);
  cls->d_reinit = true;
  cls->d_reinternalizeAtoms = reinternalizeAtoms;
  if (scopeLvl >= d_clausesToReinit.size())
  {
    d_clausesToReinit.resize(scopeLvl + 1);
  }
  d_clausesToReinit[scopeLvl].push_back(cls);
}

uint32_t PropCore::getMaxIscopeLvl(size_t numLits, const Literal* lits) const
{
  uint32_t r = 0;
  for (size_t i = 0; i < numLits; ++i)
  {
    uint32_t ilvl = getInternLevel(lits[i].var());
    if (ilvl > r)
    {
      r = ilvl;
    }
  }
  return r;
}

bool PropCore::useBinaryClauseOpt(Literal l1, Literal l2, bool lemma) const
{
  if (!binaryClauseOptEnabled())
  {
    return false;
  }
  // With relevancy enabled, binary clauses must not be used: when a learned
  // clause becomes unit it has to mark the unit literal relevant, and the
  // binary clause encoding cannot distinguish learned from non-learned
  // clauses.
  if (lemma && d_ctx.relevancyLvl() >= 2)
  {
    return false;
  }
  if (d_baseLvl > 0)
  {
    return false;
  }
  if (!lemma && d_scopeLvl > 0)
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

int PropCore::selectLearnedWatchLit(const Clause* cls) const
{
  // The learned clauses produced by conflict resolution have the property
  // that the first literal is implied after backtracking, so it is always the
  // first watch. The second watch is the literal with the highest decision
  // level. An unassigned literal was re-created after backtracking, so its
  // level is taken to be the current scope level.
  Assert(cls->getNumLiterals() >= 2);
  int maxFalseIdx = -1;
  uint32_t maxLvl = 0;
  int numLits = static_cast<int>(cls->getNumLiterals());
  for (int i = 1; i < numLits; ++i)
  {
    Literal l = cls->getLiteral(i);
    LBool val = getAssignment(l);
    Assert(val == L_FALSE || val == L_UNDEF);
    uint32_t lvl = val == L_FALSE ? getAssignLevel(l) : d_scopeLvl;
    if (maxFalseIdx == -1 || lvl > maxLvl)
    {
      maxFalseIdx = i;
      maxLvl = lvl;
    }
  }
  return maxFalseIdx;
}

int PropCore::selectWatchLit(const Clause* cls, int startingAt) const
{
  // Pick a watch literal from the positions at or after startingAt:
  //
  //  1. a true literal with the smallest assignment level, which keeps the
  //     clause inactive for as long as possible;
  //  2. otherwise an unassigned literal;
  //  3. otherwise the false literal with the largest assignment level.
  //
  // Rule 3 is what keeps Boolean propagation complete.
  Assert(cls->getNumLiterals() >= 2);
  int minTrueIdx = -1;
  int maxFalseIdx = -1;
  int unknownIdx = -1;
  int n = static_cast<int>(cls->getNumLiterals());
  for (int i = startingAt; i < n; ++i)
  {
    Literal l = cls->getLiteral(i);
    switch (getAssignment(l))
    {
      case L_FALSE:
        if (maxFalseIdx == -1
            || getAssignLevel(l.var())
                   > getAssignLevel(cls->getLiteral(maxFalseIdx).var()))
        {
          maxFalseIdx = i;
        }
        break;
      case L_UNDEF: unknownIdx = i; break;
      case L_TRUE:
        if (minTrueIdx == -1
            || getAssignLevel(l.var())
                   < getAssignLevel(cls->getLiteral(minTrueIdx).var()))
        {
          minTrueIdx = i;
        }
        break;
    }
  }
  if (minTrueIdx != -1)
  {
    return minTrueIdx;
  }
  if (unknownIdx != -1)
  {
    return unknownIdx;
  }
  Assert(maxFalseIdx != -1);
  return maxFalseIdx;
}

void PropCore::addWatchLiteral(Clause* cls, size_t idx)
{
  Assert(idx == 0 || idx == 1);
  Literal l = cls->getLiteral(idx);
  d_watches[(~l).index()].insertClause(cls);
}

Clause* PropCore::mkClause(size_t numLits,
                           Literal* lits,
                           Justification* j,
                           ClauseKind k,
                           ClauseDelEh* delEh)
{
  LiteralVector simpLits;
  switch (k)
  {
    case CLS_TH_AXIOM:
    case CLS_AUX:
    {
      if (!simplifyAuxClauseLiterals(numLits, lits, simpLits))
      {
        if (j != nullptr && !j->inRegion())
        {
          j->delEh();
          delete j;
        }
        return nullptr;  // the clause is equivalent to true
      }
      if (!simpLits.empty())
      {
        j = d_ctx.mkJustification(UnitResolutionJustification(
            d_ctx, j, simpLits.size(), simpLits.data()));
      }
      break;
    }
    case CLS_TH_LEMMA:
      if (!simplifyAuxLemmaLiterals(numLits, lits))
      {
        if (j != nullptr && !j->inRegion())
        {
          j->delEh();
          delete j;
        }
        return nullptr;  // the clause is equivalent to true
      }
      // simplifyAuxLemmaLiterals does not delete literals assigned to false,
      // so no unit resolution justification is needed.
      break;
    case CLS_LEARNED: addScores(numLits, lits); break;
  }

  uint32_t activity = 1;
  bool lemma = isLemma(k);
  d_stats.d_numMkLits += numLits;

  switch (numLits)
  {
    case 0:
      if (j != nullptr && !j->inRegion())
      {
        d_ctx.addJustification(j);
      }
      setConflict(j == nullptr ? BJustification::mkAxiom() : BJustification(j));
      Assert(inconsistent());
      return nullptr;
    case 1:
    {
      Literal unit = lits[0];
      if (j != nullptr && !j->inRegion())
      {
        d_ctx.addJustification(j);
      }
      assign(unit, j);
      incRef(unit);
      return nullptr;
    }
    case 2:
      if (useBinaryClauseOpt(lits[0], lits[1], lemma))
      {
        Literal l1 = lits[0];
        Literal l2 = lits[1];
        incRef(l1);
        incRef(l2);
        d_watches[(~l1).index()].insertLiteral(l2);
        d_watches[(~l2).index()].insertLiteral(l1);
        if (getAssignment(l1) == L_FALSE)
        {
          assign(l2, BJustification(~l1));
        }
        else if (getAssignment(l2) == L_FALSE)
        {
          assign(l1, BJustification(~l2));
        }
        d_stats.d_numMkBinClause++;
        return nullptr;
      }
      CVC5_FALLTHROUGH;
    default:
    {
      d_stats.d_numMkClause++;
      uint32_t iscopeLvl = lemma ? getMaxIscopeLvl(numLits, lits) : 0;
      Assert(d_scopeLvl >= iscopeLvl);
      bool saveAtoms = lemma && iscopeLvl > d_baseLvl;
      bool reinit = saveAtoms;
      Assert(!lemma || j == nullptr || !j->inRegion());
      Clause* cls =
          Clause::mk(numLits, lits, k, j, delEh, saveAtoms, &d_boolVar2Expr);
      if (lemma)
      {
        cls->setActivity(activity);
        if (k == CLS_LEARNED)
        {
          int w2Idx = selectLearnedWatchLit(cls);
          cls->swapLits(1, w2Idx);
        }
        else
        {
          Assert(k == CLS_TH_LEMMA);
          int w1Idx = selectWatchLit(cls, 0);
          cls->swapLits(0, w1Idx);
          int w2Idx = selectWatchLit(cls, 1);
          cls->swapLits(1, w2Idx);
        }
        d_lemmas.push_back(cls);
        addWatchLiteral(cls, 0);
        addWatchLiteral(cls, 1);
        if (getAssignment(cls->getLiteral(0)) == L_FALSE)
        {
          setConflict(BJustification(cls));
          if (k == CLS_TH_LEMMA && d_scopeLvl > d_baseLvl)
          {
            reinit = true;
            iscopeLvl = d_scopeLvl;
          }
        }
        else if (getAssignment(cls->getLiteral(1)) == L_FALSE)
        {
          assign(cls->getLiteral(0), BJustification(cls));
          if (k == CLS_TH_LEMMA && d_scopeLvl > d_baseLvl)
          {
            reinit = true;
            iscopeLvl = d_scopeLvl;
          }
        }
        if (reinit)
        {
          markForReinit(cls, iscopeLvl, saveAtoms);
        }
      }
      else
      {
        d_auxClauses.push_back(cls);
        addWatchLiteral(cls, 0);
        addWatchLiteral(cls, 1);
        if (getAssignment(cls->getLiteral(0)) == L_FALSE)
        {
          setConflict(BJustification(cls));
        }
        else if (getAssignment(cls->getLiteral(1)) == L_FALSE)
        {
          assign(cls->getLiteral(0), BJustification(cls));
        }
      }

      addLitOccs(*cls);
      return cls;
    }
  }
}

void PropCore::mkClause(Literal l1, Literal l2, Justification* j)
{
  Literal ls[2] = {l1, l2};
  mkClause(2, ls, j);
}

void PropCore::mkClause(Literal l1, Literal l2, Literal l3, Justification* j)
{
  Literal ls[3] = {l1, l2, l3};
  mkClause(3, ls, j);
}

}  // namespace z3
}  // namespace cvc5::internal
