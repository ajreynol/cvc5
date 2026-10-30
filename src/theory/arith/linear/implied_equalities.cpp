/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The equalities implied by the rows of the tableau whose variables are fixed
 * but one or two.
 */

#include "theory/arith/linear/implied_equalities.h"

#include <algorithm>

#include "theory/arith/linear/congruence_manager.h"
#include "theory/arith/linear/partial_model.h"
#include "theory/arith/linear/tableau.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

ImpliedEqualities::ImpliedEqualities(Env& env,
                                     const ArithVariables& vars,
                                     const Tableau& tableau,
                                     ArithCongruenceManager& cm)
    : EnvObj(env),
      d_vars(vars),
      d_tableau(tableau),
      d_cm(cm),
      d_offsets(context())
{
}

bool ImpliedEqualities::isFixed(ArithVar x) const
{
  return d_vars.boundsAreEqual(x)
         && d_vars.getLowerBound(x).infinitesimalIsZero();
}

const Rational& ImpliedEqualities::fixedValue(ArithVar x) const
{
  return d_vars.getLowerBound(x).getNoninfinitesimalPart();
}

bool ImpliedEqualities::isTerm(ArithVar x) const
{
  return d_cm.hasTerm(d_vars.asNode(x));
}

void ImpliedEqualities::check()
{
  for (ArithVar x : d_bounded)
  {
    // x may have been fixed by an assertion that was since backtracked
    if (!isFixed(x))
    {
      continue;
    }
    for (Tableau::ColIterator it = d_tableau.colIterator(x); !it.atEnd(); ++it)
    {
      checkRow((*it).getRowIndex());
      if (d_cm.inConflict())
      {
        d_bounded.clear();
        return;
      }
    }
  }
  d_bounded.clear();
}

void ImpliedEqualities::checkRow(RowIndex rid)
{
  // The row is sum_j a_j * v_j = 0. Find its variables that are not fixed,
  // and stop if there are more than two.
  ArithVar vars[2];
  Rational coeffs[2];
  size_t numVars = 0;
  for (Tableau::RowIterator it = d_tableau.ridRowIterator(rid); !it.atEnd();
       ++it)
  {
    ArithVar v = (*it).getColVar();
    if (!isFixed(v))
    {
      if (numVars == 2)
      {
        return;
      }
      vars[numVars] = v;
      coeffs[numVars] = (*it).getCoefficient();
      numVars++;
    }
  }
  if (numVars == 0 || (numVars == 2 && coeffs[0] != -coeffs[1]))
  {
    return;
  }
  // a * x (- a * y) = sum_j -a_j * v_j over the fixed v_j, of value k
  FixedSum sum;
  Rational k;
  for (Tableau::RowIterator it = d_tableau.ridRowIterator(rid); !it.atEnd();
       ++it)
  {
    ArithVar v = (*it).getColVar();
    if (v != vars[0] && (numVars == 1 || v != vars[1]))
    {
      Rational c = -(*it).getCoefficient() / coeffs[0];
      k += c * fixedValue(v);
      sum.emplace_back(v, c);
    }
  }
  if (numVars == 1)
  {
    assertEquality(vars[0], ARITHVAR_SENTINEL, k, sum);
  }
  else if (k.isZero())
  {
    assertEquality(vars[0], vars[1], k, sum);
  }
  else
  {
    addOffset(vars[0], vars[1], k, sum);
    for (std::pair<ArithVar, Rational>& p : sum)
    {
      p.second = -p.second;
    }
    addOffset(vars[1], vars[0], -k, sum);
  }
}

void ImpliedEqualities::addOffset(ArithVar x,
                                  ArithVar y,
                                  const Rational& k,
                                  const FixedSum& sum)
{
  OffsetKey key(y, k);
  auto it = d_offsets.find(key);
  if (it == d_offsets.end())
  {
    d_offsets.insert(key, Offset{x, sum});
    return;
  }
  const Offset& z = it->second;
  if (z.d_var == x)
  {
    return;
  }
  // x - z = (x - y) - (z - y), where the fixed variables common to both sums
  // are combined
  FixedSum diff = sum;
  for (const std::pair<ArithVar, Rational>& p : z.d_sum)
  {
    diff.emplace_back(p.first, -p.second);
  }
  std::sort(diff.begin(), diff.end(), [](const auto& a, const auto& b) {
    return a.first < b.first;
  });
  size_t j = 0;
  for (size_t i = 0; i < diff.size(); i++)
  {
    if (j > 0 && diff[j - 1].first == diff[i].first)
    {
      diff[j - 1].second += diff[i].second;
    }
    else
    {
      diff[j++] = diff[i];
    }
  }
  diff.resize(j);
  diff.erase(std::remove_if(diff.begin(),
                            diff.end(),
                            [](const auto& p) { return p.second.isZero(); }),
             diff.end());
  assertEquality(x, z.d_var, Rational(0), diff);
}

void ImpliedEqualities::assertEquality(ArithVar x,
                                       ArithVar y,
                                       const Rational& k,
                                       const FixedSum& sum)
{
  if (sum.empty() || !isTerm(x) || (y != ARITHVAR_SENTINEL && !isTerm(y)))
  {
    return;
  }
  Node a = d_vars.asNode(x);
  Node b;
  if (y == ARITHVAR_SENTINEL)
  {
    if (d_vars.isInteger(x) && !k.isIntegral())
    {
      // the simplex has yet to find this conflict
      return;
    }
    b = nodeManager()->mkConstRealOrInt(a.getType(), k);
  }
  else
  {
    b = d_vars.asNode(y);
  }
  d_cm.impliedEquality(a, b, sum);
}

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
