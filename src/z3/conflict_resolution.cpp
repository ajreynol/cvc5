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

#include "z3/explainer.h"
#include "z3/smt_context.h"
#include "z3/theory.h"

namespace cvc5::internal {
namespace z3 {

ConflictResolution::ConflictResolution(SmtContext& ctx,
                                       Explainer& explainer,
                                       const Params& params,
                                       const LiteralVector& assignedLiterals)
    : d_params(params),
      d_ctx(ctx),
      d_explainer(explainer),
      d_assignedLiterals(assignedLiterals),
      d_conflictLvl(0),
      d_newScopeLvl(0),
      d_lemmaIscopeLvl(0)
{
}

uint32_t ConflictResolution::getJustificationMaxLvl(Justification* js)
{
  uint32_t r = 0;
  LiteralVector& antecedents = d_tmpLiteralVector;
  antecedents.clear();
  d_explainer.justification2Literals(js, antecedents);
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

void ConflictResolution::processAntecedent(Literal antecedent, size_t& numMarks)
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

void ConflictResolution::processJustification(Literal /*consequent*/,
                                              Justification* js,
                                              size_t& numMarks)
{
  LiteralVector& antecedents = d_tmpLiteralVector;
  antecedents.clear();
  d_explainer.explain(js, antecedents);
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
    return false;
  }

  Assert(!d_assignedLiterals.empty());
  Assert(d_explainer.isClear());
  return true;
}

void ConflictResolution::finalizeResolve(BJustification /*conflict*/,
                                         Literal /*notL*/)
{
  d_explainer.rollback(0);

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
                                                      size_t oldCheckpoint)
{
  resetUnmark(oldSize);
  d_explainer.rollback(oldCheckpoint);
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

bool ConflictResolution::processJustificationForMinimization(Justification* js)
{
  LiteralVector& antecedents = d_tmpLiteralVector;
  antecedents.clear();
  // Note explain does not reset the caches of visited justifications and
  // equalities; resetUnmarkAndJustifications does that.
  d_explainer.explain(js, antecedents);
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
  size_t oldCheckpoint = d_explainer.getCheckpoint();

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
              resetUnmarkAndJustifications(oldSize, oldCheckpoint);
              return false;
            }
          }
        }
        Justification* cjs = cls->getJustification();
        if (cjs != nullptr && !processJustificationForMinimization(cjs))
        {
          resetUnmarkAndJustifications(oldSize, oldCheckpoint);
          return false;
        }
        break;
      }
      case BJustification::BIN_CLAUSE:
        if (!processAntecedentForMinimization(js.getLiteral()))
        {
          resetUnmarkAndJustifications(oldSize, oldCheckpoint);
          return false;
        }
        break;
      case BJustification::AXIOM:
        // it is a decision variable from a previous scope level, or an
        // assumption
        if (d_ctx.getAssignLevel(var) > d_ctx.getBaseLevel())
        {
          resetUnmarkAndJustifications(oldSize, oldCheckpoint);
          return false;
        }
        break;
      case BJustification::JUSTIFICATION:
        if (!processJustificationForMinimization(js.getJustification()))
        {
          resetUnmarkAndJustifications(oldSize, oldCheckpoint);
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
  // In Z3 this resets the proof-generation caches only, which this port does
  // not have, so there is nothing to do. In particular the lemma must *not*
  // be cleared here: popScopeCore calls this while resolveConflict is still
  // rebuilding the literals and atoms of the lemma it just derived.
}

ConflictResolution* mkConflictResolution(SmtContext& ctx,
                                         Explainer& explainer,
                                         const Params& params,
                                         const LiteralVector& assignedLiterals)
{
  return new ConflictResolution(ctx, explainer, params, assignedLiterals);
}

}  // namespace z3
}  // namespace cvc5::internal
