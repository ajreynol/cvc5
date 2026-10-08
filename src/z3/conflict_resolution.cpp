/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Conflict resolution.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_conflict_resolution.cpp, and recast in cvc5 style.
 */

#include "z3/conflict_resolution.h"

#include <algorithm>

#include "z3/smt_context.h"
#include "z3/theory.h"

namespace cvc5::internal {
namespace z3 {

ConflictResolution::ConflictResolution(SmtContext& ctx,
                                       DynAckManager& dynAckManager,
                                       const Params& params,
                                       const LiteralVector& assignedLiterals,
                                       std::vector<WatchList>& watches)
    : d_params(params),
      d_ctx(ctx),
      d_dynAckManager(dynAckManager),
      d_assignedLiterals(assignedLiterals),
      d_conflictLvl(0),
      d_newScopeLvl(0),
      d_lemmaIscopeLvl(0),
      d_todoJsQhead(0),
      d_antecedents(nullptr),
      d_watches(watches)
{
}

template <bool Set>
void ConflictResolution::markENodesInTrans(ENode* n)
{
  while (n != nullptr)
  {
    if (Set)
    {
      n->setMark2();
    }
    else
    {
      n->unsetMark2();
    }
    n = n->d_trans.d_target;
  }
}

ENode* ConflictResolution::findCommonAncestor(ENode* n1, ENode* n2)
{
  // Find a common ancestor of n1 and n2 in the proof forest, so that the
  // shared suffix up to the root is left out of the transitivity proof:
  //
  //   n1 = a1 = ... = ai = ANC = ... = root
  //   n2 = b1 = ... = bj = ANC = ... = root
  //
  // giving the irredundant proof n1 = a1 = ... = ai = ANC = bj = ... = n2.
  Assert(n1->getRoot() == n2->getRoot());
  markENodesInTrans<true>(n1);
  while (true)
  {
    Assert(n2 != nullptr);
    if (n2->isMarked2())
    {
      markENodesInTrans<false>(n1);
      return n2;
    }
    n2 = n2->d_trans.d_target;
  }
}

void ConflictResolution::eqJustification2Literals(ENode* lhs,
                                                  ENode* rhs,
                                                  EqJustification js)
{
  Assert(d_antecedents != nullptr);
  switch (js.getKind())
  {
    case EqJustification::AXIOM: break;
    case EqJustification::EQUATION:
      d_antecedents->push_back(js.getLiteral());
      break;
    case EqJustification::JUSTIFICATION:
      markJustification(js.getJustification());
      break;
    case EqJustification::CONGRUENCE:
    {
      d_dynAckManager.usedCgEh(lhs->getExpr(), rhs->getExpr());
      uint32_t numArgs = lhs->getNumArgs();
      Assert(numArgs == rhs->getNumArgs());
      if (js.usedCommutativity())
      {
        Assert(numArgs == 2);
        markEq(lhs->getArg(0), rhs->getArg(1));
        markEq(lhs->getArg(1), rhs->getArg(0));
      }
      else
      {
        for (uint32_t i = 0; i < numArgs; ++i)
        {
          markEq(lhs->getArg(i), rhs->getArg(i));
        }
      }
      break;
    }
  }
}

void ConflictResolution::eqBranch2Literals(ENode* n1, ENode* n2)
{
  while (n1 != n2)
  {
    eqJustification2Literals(
        n1, n1->d_trans.d_target, n1->d_trans.d_justification);
    n1 = n1->d_trans.d_target;
  }
}

void ConflictResolution::eq2Literals(ENode* n1, ENode* n2)
{
  ENode* c = findCommonAncestor(n1, n2);
  eqBranch2Literals(n1, c);
  eqBranch2Literals(n2, c);
  d_dynAckManager.usedEqEh(n1->getExpr(), n2->getExpr(), c->getExpr());
}

void ConflictResolution::justification2LiteralsCore(Justification* js,
                                                    LiteralVector& result)
{
  Assert(d_todoJsQhead <= d_todoJs.size());
  d_antecedents = &result;
  markJustification(js);
  processJustifications();
}

void ConflictResolution::processJustifications()
{
  while (true)
  {
    size_t sz = d_todoJs.size();
    while (d_todoJsQhead < sz)
    {
      Justification* js = d_todoJs[d_todoJsQhead];
      d_todoJsQhead++;
      js->getAntecedents(*this);
    }
    while (!d_todoEqs.empty())
    {
      ENodePair p = d_todoEqs.back();
      d_todoEqs.pop_back();
      eq2Literals(p.first, p.second);
    }
    if (d_todoJsQhead == d_todoJs.size())
    {
      d_antecedents = nullptr;
      return;
    }
  }
}

void ConflictResolution::unmarkJustifications(size_t oldJsQhead)
{
  Assert(oldJsQhead <= d_todoJs.size());
  for (size_t i = oldJsQhead, sz = d_todoJs.size(); i < sz; ++i)
  {
    d_todoJs[i]->unsetMark();
  }
  d_todoJs.resize(oldJsQhead);
  d_todoJsQhead = oldJsQhead;
  d_todoEqs.clear();
  d_alreadyProcessedEqs.clear();
}

void ConflictResolution::justification2Literals(Justification* js,
                                                LiteralVector& result)
{
  Assert(d_todoJs.empty());
  Assert(d_todoJsQhead == 0);
  Assert(d_todoEqs.empty());
  justification2LiteralsCore(js, result);
  unmarkJustifications(0);
  Assert(d_todoEqs.empty());
}

void ConflictResolution::eq2Literals(ENode* n1,
                                     ENode* n2,
                                     LiteralVector& result)
{
  Assert(d_todoJs.empty());
  Assert(d_todoJsQhead == 0);
  Assert(d_todoEqs.empty());
  d_antecedents = &result;
  d_todoEqs.push_back(ENodePair(n1, n2));
  processJustifications();
  unmarkJustifications(0);
  Assert(d_todoEqs.empty());
}

uint32_t ConflictResolution::getJustificationMaxLvl(Justification* js)
{
  uint32_t r = 0;
  LiteralVector& antecedents = d_tmpLiteralVector;
  antecedents.clear();
  justification2Literals(js, antecedents);
  for (Literal lit : antecedents)
  {
    r = std::max(r, d_ctx.getAssignLevel(lit));
  }
  return r;
}

uint32_t ConflictResolution::getMaxLvl(Literal consequent, BJustification js)
{
  uint32_t r = 0;
  if (consequent != s_falseLiteral)
  {
    r = d_ctx.getAssignLevel(consequent);
  }

  switch (js.getKind())
  {
    case BJustification::CLAUSE:
    {
      Clause* cls = js.getClause();
      size_t numLits = cls->getNumLiterals();
      size_t i = 0;
      if (consequent != s_falseLiteral)
      {
        Assert((*cls)[0] == consequent || (*cls)[1] == consequent);
        if ((*cls)[0] == consequent)
        {
          i = 1;
        }
        else
        {
          r = std::max(r, d_ctx.getAssignLevel((*cls)[0]));
          i = 2;
        }
      }
      for (; i < numLits; ++i)
      {
        r = std::max(r, d_ctx.getAssignLevel((*cls)[i]));
      }
      Justification* cjs = cls->getJustification();
      if (cjs != nullptr)
      {
        r = std::max(r, getJustificationMaxLvl(cjs));
      }
      break;
    }
    case BJustification::BIN_CLAUSE:
      r = std::max(r, d_ctx.getAssignLevel(js.getLiteral()));
      break;
    case BJustification::AXIOM: break;
    case BJustification::JUSTIFICATION:
      r = std::max(r, getJustificationMaxLvl(js.getJustification()));
      break;
  }
  return r;
}

void ConflictResolution::processAntecedent(Literal antecedent,
                                           size_t& numMarks)
{
  BoolVar var = antecedent.var();
  uint32_t lvl = d_ctx.getAssignLevel(var);
  Assert(var < d_ctx.getNumBoolVars());

  if (!d_ctx.isMarked(var) && lvl > d_ctx.getBaseLevel())
  {
    d_ctx.setMark(var);
    d_ctx.incBvarActivity(var);
    TNode n = d_ctx.boolVar2Expr(var);
    if (!n.isNull() && isApp(n))
    {
      Theory* th = d_ctx.getTheory(familyIdOf(n));
      if (th != nullptr)
      {
        th->conflictResolutionEh(n, var);
      }
    }

    if (lvl == d_conflictLvl)
    {
      numMarks++;
    }
    else
    {
      d_lemma.push_back(~antecedent);
      d_lemmaAtoms.push_back(d_ctx.boolVar2Expr(var));
    }
  }
}

void ConflictResolution::processJustification(Literal consequent,
                                              Justification* js,
                                              size_t& numMarks)
{
  LiteralVector& antecedents = d_tmpLiteralVector;
  antecedents.clear();
  justification2LiteralsCore(js, antecedents);
  for (Literal l : antecedents)
  {
    processAntecedent(l, numMarks);
  }
}

size_t ConflictResolution::skipLiteralsAboveConflictLevel()
{
  size_t idx = d_assignedLiterals.size();
  if (idx == 0)
  {
    return idx;
  }
  idx--;
  // skip literals from levels above the conflict level
  while (d_ctx.getAssignLevel(d_assignedLiterals[idx]) > d_conflictLvl
         && idx > 0)
  {
    idx--;
  }
  return idx;
}

bool ConflictResolution::initializeResolve(BJustification conflict,
                                           Literal notL,
                                           BJustification& js,
                                           Literal& consequent)
{
  d_lemma.clear();
  d_lemmaAtoms.clear();
  Assert(d_ctx.getSearchLevel() >= d_ctx.getBaseLevel());
  js = conflict;
  consequent = s_falseLiteral;
  if (notL != s_nullLiteral)
  {
    consequent = ~notL;
  }

  d_conflictLvl = getMaxLvl(consequent, js);

  // The conflict level can be smaller than the search level when there are
  // user scopes and the previous levels were already inconsistent, or the
  // inconsistency was triggered by an axiom, both of which count as level
  // zero.
  if (d_conflictLvl <= d_ctx.getSearchLevel())
  {
    Trace("z3-conflict") << "problem is unsat" << std::endl;
    if (d_ctx.trackingAssumptions())
    {
      mkUnsatCore(conflict, notL);
    }
    return false;
  }

  Assert(!d_assignedLiterals.empty());
  Assert(d_todoJs.empty());
  Assert(d_todoJsQhead == 0);
  Assert(d_todoEqs.empty());
  return true;
}

void ConflictResolution::finalizeResolve(BJustification conflict,
                                         Literal notL)
{
  unmarkJustifications(0);

  if (d_params.d_minimizeLemmas)
  {
    minimizeLemma();
  }

  d_newScopeLvl = d_ctx.getSearchLevel();
  d_lemmaIscopeLvl = d_ctx.getInternLevel(d_lemma[0].var());
  Assert(!d_ctx.isMarked(d_lemma[0].var()));
  for (size_t i = 1, sz = d_lemma.size(); i < sz; ++i)
  {
    BoolVar var = d_lemma[i].var();
    if (var != s_nullBoolVar)
    {
      d_ctx.unsetMark(var);
      uint32_t lvl = d_ctx.getAssignLevel(var);
      if (lvl > d_newScopeLvl)
      {
        d_newScopeLvl = lvl;
      }
      lvl = d_ctx.getInternLevel(var);
      if (lvl > d_lemmaIscopeLvl)
      {
        d_lemmaIscopeLvl = lvl;
      }
    }
  }
}

bool ConflictResolution::resolve(BJustification conflict, Literal notL)
{
  BJustification js;
  Literal consequent;

  if (!initializeResolve(conflict, notL, js, consequent))
  {
    return false;
  }

  size_t idx = skipLiteralsAboveConflictLevel();

  // save space for the first UIP
  d_lemma.push_back(s_nullLiteral);
  d_lemmaAtoms.push_back(Node::null());

  size_t numMarks = 0;
  if (notL != s_nullLiteral)
  {
    processAntecedent(notL, numMarks);
  }

  do
  {
    Assert(js != s_nullBJustification);
    switch (js.getKind())
    {
      case BJustification::CLAUSE:
      {
        Clause* cls = js.getClause();
        if (cls->isLemma())
        {
          cls->incClauseActivity();
        }
        size_t numLits = cls->getNumLiterals();
        size_t i = 0;
        if (consequent != s_falseLiteral)
        {
          Assert((*cls)[0] == consequent || (*cls)[1] == consequent);
          if ((*cls)[0] == consequent)
          {
            i = 1;
          }
          else
          {
            Literal l = (*cls)[0];
            Assert(consequent.var() != l.var());
            processAntecedent(~l, numMarks);
            i = 2;
          }
        }
        for (; i < numLits; ++i)
        {
          Literal l = (*cls)[i];
          Assert(consequent.var() != l.var());
          processAntecedent(~l, numMarks);
        }
        Justification* cjs = cls->getJustification();
        if (cjs != nullptr)
        {
          processJustification(consequent, cjs, numMarks);
        }
        break;
      }
      case BJustification::BIN_CLAUSE:
        Assert(consequent.var() != js.getLiteral().var());
        processAntecedent(js.getLiteral(), numMarks);
        break;
      case BJustification::AXIOM: break;
      case BJustification::JUSTIFICATION:
        processJustification(consequent, js.getJustification(), numMarks);
        break;
    }

    while (true)
    {
      Literal l = d_assignedLiterals[idx];
      if (d_ctx.isMarked(l.var()))
      {
        break;
      }
      Assert(d_ctx.getAssignLevel(l) == d_conflictLvl
             // it may also be an (out-of-order) asserted literal
             || d_ctx.getAssignLevel(l) == d_ctx.getBaseLevel());
      Assert(idx > 0);
      idx--;
    }

    consequent = d_assignedLiterals[idx];
    BoolVar cVar = consequent.var();
    Assert(d_ctx.getAssignLevel(cVar) == d_conflictLvl);
    js = d_ctx.getJustification(cVar);
    idx--;
    numMarks--;
    d_ctx.unsetMark(cVar);
  } while (numMarks > 0);

  d_lemma[0] = ~consequent;
  d_lemmaAtoms[0] = d_ctx.boolVar2Expr(consequent.var());

  finalizeResolve(conflict, notL);

  return true;
}

LevelApproxSet ConflictResolution::getLemmaApproxLevelSet()
{
  LevelApproxSet result;
  for (Literal l : d_lemma)
  {
    result.insert(d_ctx.getAssignLevel(l));
  }
  return result;
}

void ConflictResolution::resetUnmark(size_t oldSize)
{
  size_t currSize = d_unmark.size();
  for (size_t i = oldSize; i < currSize; ++i)
  {
    d_ctx.unsetMark(d_unmark[i]);
  }
  d_unmark.resize(oldSize);
}

void ConflictResolution::resetUnmarkAndJustifications(size_t oldSize,
                                                      size_t oldJsQhead)
{
  resetUnmark(oldSize);
  unmarkJustifications(oldJsQhead);
}

bool ConflictResolution::processAntecedentForMinimization(Literal antecedent)
{
  BoolVar var = antecedent.var();
  uint32_t lvl = d_ctx.getAssignLevel(var);
  if (!d_ctx.isMarked(var) && lvl > d_ctx.getBaseLevel())
  {
    if (d_lvlSet.mayContain(lvl))
    {
      d_ctx.setMark(var);
      d_unmark.push_back(var);
      d_lemmaMinStack.push_back(var);
    }
    else
    {
      return false;
    }
  }
  return true;
}

bool ConflictResolution::processJustificationForMinimization(
    Justification* js)
{
  LiteralVector& antecedents = d_tmpLiteralVector;
  antecedents.clear();
  // Note justification2LiteralsCore does not reset the caches of visited
  // justifications and equalities; resetUnmarkAndJustifications does that.
  justification2LiteralsCore(js, antecedents);
  for (Literal l : antecedents)
  {
    if (!processAntecedentForMinimization(l))
    {
      return false;
    }
  }
  return true;
}

bool ConflictResolution::impliedByMarked(Literal lit)
{
  // True if lit is implied by other marked literals and/or literals assigned
  // at the base level. The level approximation lets the search stop early:
  // as soon as a literal is assigned at a level outside the lemma's level set
  // it cannot be implied by the lemma.
  d_lemmaMinStack.clear();  // avoid a recursive function
  d_lemmaMinStack.push_back(lit.var());
  size_t oldSize = d_unmark.size();
  size_t oldJsQhead = d_todoJsQhead;

  while (!d_lemmaMinStack.empty())
  {
    BoolVar var = d_lemmaMinStack.back();
    d_lemmaMinStack.pop_back();
    BJustification js = d_ctx.getJustification(var);
    Assert(js != s_nullBJustification);
    switch (js.getKind())
    {
      case BJustification::CLAUSE:
      {
        Clause* cls = js.getClause();
        size_t numLits = cls->getNumLiterals();
        size_t pos = ((*cls)[1].var() == var) ? 1 : 0;
        for (size_t i = 0; i < numLits; ++i)
        {
          if (pos != i)
          {
            Literal l = (*cls)[i];
            Assert(l.var() != var);
            if (!processAntecedentForMinimization(~l))
            {
              resetUnmarkAndJustifications(oldSize, oldJsQhead);
              return false;
            }
          }
        }
        Justification* cjs = cls->getJustification();
        if (cjs != nullptr && !processJustificationForMinimization(cjs))
        {
          resetUnmarkAndJustifications(oldSize, oldJsQhead);
          return false;
        }
        break;
      }
      case BJustification::BIN_CLAUSE:
        if (!processAntecedentForMinimization(js.getLiteral()))
        {
          resetUnmarkAndJustifications(oldSize, oldJsQhead);
          return false;
        }
        break;
      case BJustification::AXIOM:
        // it is a decision variable from a previous scope level, or an
        // assumption
        if (d_ctx.getAssignLevel(var) > d_ctx.getBaseLevel())
        {
          resetUnmarkAndJustifications(oldSize, oldJsQhead);
          return false;
        }
        break;
      case BJustification::JUSTIFICATION:
        if (d_ctx.isAssumption(var)
            || !processJustificationForMinimization(js.getJustification()))
        {
          resetUnmarkAndJustifications(oldSize, oldJsQhead);
          return false;
        }
        break;
    }
  }
  return true;
}

void ConflictResolution::minimizeLemma()
{
  // Remove the literals of the lemma that are implied by the other literals
  // of the lemma and/or literals assigned at the base levels.
  d_unmark.clear();

  d_lvlSet = getLemmaApproxLevelSet();

  size_t sz = d_lemma.size();
  size_t i = 1;  // the first literal is the FUIP
  size_t j = 1;
  for (; i < sz; ++i)
  {
    Literal l = d_lemma[i];
    if (impliedByMarked(l))
    {
      d_unmark.push_back(l.var());
    }
    else
    {
      if (j != i)
      {
        d_lemma[j] = l;
        d_lemmaAtoms[j] = d_lemmaAtoms[i];
      }
      j++;
    }
  }

  resetUnmarkAndJustifications(0, 0);
  d_lemma.resize(j);
  d_lemmaAtoms.resize(j);
  d_ctx.getStats().d_numMinimizedLits += sz - j;
}

void ConflictResolution::reset()
{
  d_todoJs.clear();
  d_todoJsQhead = 0;
  d_todoEqs.clear();
  d_alreadyProcessedEqs.clear();
  d_lemma.clear();
  d_lemmaAtoms.clear();
  d_assumptions.clear();
  d_unmark.clear();
  d_lemmaMinStack.clear();
}

void ConflictResolution::processAntecedentForUnsatCore(Literal antecedent)
{
  BoolVar var = antecedent.var();
  if (!d_ctx.isMarked(var))
  {
    d_ctx.setMark(var);
    d_unmark.push_back(var);
  }
  if (d_ctx.isAssumption(var))
  {
    d_assumptions.push_back(antecedent);
  }
}

void ConflictResolution::processJustificationForUnsatCore(Justification* js)
{
  LiteralVector& antecedents = d_tmpLiteralVector;
  antecedents.clear();
  justification2LiteralsCore(js, antecedents);
  for (Literal lit : antecedents)
  {
    processAntecedentForUnsatCore(lit);
  }
}

void ConflictResolution::mkUnsatCore(BJustification conflict, Literal notL)
{
  Assert(d_ctx.trackingAssumptions());
  d_assumptions.clear();
  d_unmark.clear();

  Assert(d_conflictLvl <= d_ctx.getSearchLevel());
  uint32_t searchLvl = d_ctx.getSearchLevel();

  BJustification js = conflict;
  Literal consequent = s_falseLiteral;
  if (notL != s_nullLiteral)
  {
    consequent = ~notL;
  }

  int64_t idx = static_cast<int64_t>(skipLiteralsAboveConflictLevel());

  if (notL != s_nullLiteral)
  {
    processAntecedentForUnsatCore(consequent);
  }

  if (!d_assignedLiterals.empty())
  {
    bool done = false;
    while (!done)
    {
      switch (js.getKind())
      {
        case BJustification::CLAUSE:
        {
          Clause* cls = js.getClause();
          size_t numLits = cls->getNumLiterals();
          size_t i = 0;
          if (consequent != s_falseLiteral)
          {
            Assert(cls->getLiteral(0) == consequent
                   || cls->getLiteral(1) == consequent);
            if (cls->getLiteral(0) == consequent)
            {
              i = 1;
            }
            else
            {
              processAntecedentForUnsatCore(~cls->getLiteral(0));
              i = 2;
            }
          }
          for (; i < numLits; ++i)
          {
            processAntecedentForUnsatCore(~cls->getLiteral(i));
          }
          Justification* cjs = cls->getJustification();
          if (cjs != nullptr)
          {
            processJustificationForUnsatCore(cjs);
          }
          break;
        }
        case BJustification::BIN_CLAUSE:
          Assert(consequent.var() != js.getLiteral().var());
          processAntecedentForUnsatCore(js.getLiteral());
          break;
        case BJustification::AXIOM: break;
        case BJustification::JUSTIFICATION:
          processJustificationForUnsatCore(js.getJustification());
          break;
      }

      if (d_ctx.isAssumption(consequent.var()))
      {
        d_assumptions.push_back(consequent);
      }
      while (idx >= 0)
      {
        Literal l = d_assignedLiterals[idx];
        if (d_ctx.getAssignLevel(l) < searchLvl)
        {
          done = true;
          break;
        }
        if (d_ctx.isMarked(l.var()))
        {
          break;
        }
        idx--;
      }
      if (done || idx < 0)
      {
        break;
      }

      consequent = d_assignedLiterals[idx];
      BoolVar cVar = consequent.var();
      Assert(d_ctx.getAssignLevel(cVar) == searchLvl);
      js = d_ctx.getJustification(cVar);
      idx--;
    }
  }

  resetUnmarkAndJustifications(0, 0);
}

ConflictResolution* mkConflictResolution(
    SmtContext& ctx,
    DynAckManager& dackManager,
    const Params& params,
    const LiteralVector& assignedLiterals,
    std::vector<WatchList>& watches)
{
  return new ConflictResolution(
      ctx, dackManager, params, assignedLiterals, watches);
}

}  // namespace z3
}  // namespace cvc5::internal
