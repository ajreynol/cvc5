/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Equality propagation of the simplex-based arithmetic solver of the ported
 * Z3 core: fixed variables and offset rows.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), file
 * src/smt/theory_arith_eq.h, and recast in cvc5 style.
 */

#include "z3/justification.h"
#include "z3/smt_context.h"
#include "z3/theory_arith.h"

namespace cvc5::internal {
namespace z3 {

/**
 * This method is invoked when a variable was non fixed and become fixed.
 */
void TheoryArith::fixedVarEh(TheoryVar v)
{
  if (!propagateEqs())
  {
    return;
  }

  Assert(isFixed(v));
  // WARNING: it is not safe to use getValue(v) here, since getValue(v) may
  // not satisfy v bounds at this point.
  if (!lowerBound(v).isRational())
  {
    return;
  }
  const Numeral& val = lowerBound(v).getRational();
  ValueSortPair key(val, isIntSrc(v));
  std::map<ValueSortPair, TheoryVar>::iterator it = d_fixedVarTable.find(key);
  if (it != d_fixedVarTable.end())
  {
    TheoryVar v2 = it->second;
    if (v2 < static_cast<int>(getNumVars()) && isFixed(v2)
        && lowerBound(v2).getRational() == val)
    {
      // It only makes sense to propagate equality to the core when v and v2
      // have the same sort. The table d_fixedVarTable is not restored during
      // backtrack. So, it may contain invalid (key -> value) pairs. So, we
      // must check whether v2 is really equal to val (previous test) AND it
      // has the same sort of v. The following test was missing in a previous
      // version of Z3.
      if (!isEqual(v, v2) && isIntSrc(v) == isIntSrc(v2))
      {
        Antecedents ante(*this);

        //
        // v <= k <= v2  => v <= v2
        // v >= k >= v2 => v >= v2
        //

        lower(v)->pushJustification(ante, Rational(0), proofsEnabled());
        upper(v2)->pushJustification(ante, Rational(0), proofsEnabled());
        lower(v2)->pushJustification(ante, Rational(0), proofsEnabled());
        upper(v)->pushJustification(ante, Rational(0), proofsEnabled());

        d_stats.d_fixedEqs++;
        propagateEqToCore(v, v2, ante);
      }
    }
    else
    {
      // the original fixed variable v2 was deleted or its bounds were removed
      // during backtracking.
      d_fixedVarTable.erase(key);
      d_fixedVarTable[key] = v;
    }
  }
  else
  {
    d_fixedVarTable[key] = v;
  }
}

/**
 * Returns true if r is a offset row. A offset row is a row that can be
 * written as:
 *
 *   x = y + M
 *
 * where x and y are non fixed variables, and M is linear polynomials where
 * all variables are fixed, and M evaluates to k. When true is returned, x, y
 * and k are stored in the given arguments.
 *
 * The following rule is used to select x and y.
 * - if the base variable is not fixed, then x is the base var.
 * - otherwise x is the smallest var.
 */
bool TheoryArith::isOffsetRow(const Row& r,
                              TheoryVar& x,
                              TheoryVar& y,
                              Numeral& k) const
{
  // Quick check without using big numbers...
  // Check if there are more than 2 unbounded vars.
  size_t bad = 0;
  std::vector<RowEntry>::const_iterator it = r.begin();
  std::vector<RowEntry>::const_iterator end = r.end();
  for (; it != end; ++it)
  {
    if (!it->isDead())
    {
      TheoryVar v = it->d_var;
      if (lower(v) != nullptr && upper(v) != nullptr)
      {
        continue;
      }
      bad++;
      if (bad > 2)
      {
        return false;
      }
    }
  }

  // Full check using == for big numbers...
  x = s_nullTheoryVar;
  y = s_nullTheoryVar;
  it = r.begin();
  for (; it != end; ++it)
  {
    if (!it->isDead())
    {
      TheoryVar v = it->d_var;
      if (isFixed(v))
      {
        continue;
      }
      if (it->d_coeff.isOne() && x == s_nullTheoryVar)
      {
        x = v;
        continue;
      }
      if (isMinusOne(it->d_coeff) && y == s_nullTheoryVar)
      {
        y = v;
        continue;
      }
      return false;
    }
  }

  if (x == s_nullTheoryVar && y == s_nullTheoryVar)
  {
    return false;
  }

  k = Rational(0);
  it = r.begin();
  for (; it != end; ++it)
  {
    if (!it->isDead())
    {
      TheoryVar v = it->d_var;
      if (v == x || v == y)
      {
        continue;
      }
      Assert(isFixed(v));
      k -= it->d_coeff * lowerBound(v).getRational();
    }
  }

  if (y == s_nullTheoryVar)
  {
    return true;
  }

  if (x == s_nullTheoryVar)
  {
    std::swap(x, y);
    k = -k;
    Assert(x != s_nullTheoryVar);
    return true;
  }

  if (r.getBaseVar() != x && x > y)
  {
    std::swap(x, y);
    k = -k;
  }
  return true;
}

/**
 * Cheap propagation of equalities x_i = x_j, when
 *   x_i = y + k
 *   x_j = y + k
 *
 * This equalities are detected by maintaining a map:
 *   (y, k) ->  row_id   when a row is of the form  x = y + k
 *
 * This methods checks whether the given row is an offset row (See
 * isOffsetRow), and uses the map to find new equalities if that is the case.
 */
void TheoryArith::propagateCheapEq(size_t rid)
{
  if (!propagateEqs())
  {
    return;
  }
  const Row& r = d_rows[rid];
  TheoryVar x;
  TheoryVar y;
  Numeral k;
  if (isOffsetRow(r, x, y, k))
  {
    if (y == s_nullTheoryVar)
    {
      // x is an implied fixed var at k.
      ValueSortPair key(k, isIntSrc(x));
      std::map<ValueSortPair, TheoryVar>::iterator itf =
          d_fixedVarTable.find(key);
      TheoryVar x2 = s_nullTheoryVar;
      if (itf != d_fixedVarTable.end())
      {
        x2 = itf->second;
      }
      if (itf != d_fixedVarTable.end() && x2 < static_cast<int>(getNumVars())
          && isFixed(x2) && lowerBound(x2).getRational() == k &&
          // We must check whether x2 is an integer.
          // The table d_fixedVarTable is not restored during backtrack. So,
          // it may contain invalid (key -> value) pairs.
          // So, we must check whether x2 is really equal to k (previous test)
          // AND has the same sort of x.
          // The following test was missing in a previous version of Z3.
          isIntSrc(x) == isIntSrc(x2) && !isEqual(x, x2))
      {
        Antecedents ante(*this);
        collectFixedVarJustifications(r, ante);

        //
        // x1 <= k1 x1 >= k1, x2 <= x1 + k2 x2 >= x1 + k2
        //
        lower(x2)->pushJustification(ante, Rational(0), proofsEnabled());
        upper(x2)->pushJustification(ante, Rational(0), proofsEnabled());
        d_stats.d_fixedEqs++;
        propagateEqToCore(x, x2, ante);
      }
      // return;
    }

    if (k.isZero() && y != s_nullTheoryVar && !isEqual(x, y)
        && isIntSrc(x) == isIntSrc(y))
    {
      // found equality x = y
      Antecedents ante(*this);
      collectFixedVarJustifications(r, ante);
      d_stats.d_offsetEqs++;
      propagateEqToCore(x, y, ante);
    }

    VarOffset key(y, k);
    std::map<VarOffset, int>::iterator ito = d_varOffset2RowId.find(key);
    if (ito != d_varOffset2RowId.end())
    {
      int rowId = ito->second;
      Row& r2 = d_rows[rowId];
      if (r.getBaseVar() == r2.getBaseVar())
      {
        // it is the same row.
        return;
      }
      TheoryVar x2;
      TheoryVar y2;
      Numeral k2;
      if (r2.getBaseVar() != s_nullTheoryVar && isOffsetRow(r2, x2, y2, k2))
      {
        bool newEq = false;
        if (y == y2 && k == k2)
        {
          newEq = true;
        }
        else if (y2 != s_nullTheoryVar)
        {
          std::swap(x2, y2);
          k2 = -k2;
          if (y == y2 && k == k2)
          {
            newEq = true;
          }
        }

        if (newEq)
        {
          if (!isEqual(x, x2) && isIntSrc(x) == isIntSrc(x2))
          {
            Assert(y == y2 && k == k2);
            Antecedents ante(*this);
            collectFixedVarJustifications(r, ante);
            collectFixedVarJustifications(r2, ante);
            d_stats.d_offsetEqs++;
            propagateEqToCore(x, x2, ante);
          }
          return;
        }
      }

      // the original row was delete or it is not offset row anymore ===>
      // remove it from table
    }
    // add new entry
    d_varOffset2RowId[key] = static_cast<int>(rid);
  }
}

void TheoryArith::propagateEqToCore(TheoryVar x,
                                    TheoryVar y,
                                    Antecedents& antecedents)
{
  // Ignore equality if variables are already known to be equal.
  if (isEqual(x, y))
  {
    return;
  }
  ENode* ex = getENode(x);
  ENode* ey = getENode(y);
  // I doesn't make sense to propagate an equality (to the core) of variables
  // of different sort.
  if (ex->getExpr().getType() != ey->getExpr().getType())
  {
    return;
  }

  const EqVector& eqs = antecedents.eqs();
  const LiteralVector& lits = antecedents.lits();
  Justification* js =
      d_ctx.mkJustification(ExtTheoryEqPropagationJustification(getId(),
                                                                d_ctx,
                                                                lits.size(),
                                                                lits.data(),
                                                                eqs.size(),
                                                                eqs.data(),
                                                                ex,
                                                                ey));
  Trace("z3-arith") << "detected equality: v" << x << " = v" << y << std::endl;
  d_ctx.assignEq(ex, ey, EqJustification(js));
}

}  // namespace z3
}  // namespace cvc5::internal
