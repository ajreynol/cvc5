/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The nonlinear part of the simplex-based arithmetic solver of the ported Z3
 * core, as far as it runs with smt.arith.nl=false.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), file
 * src/smt/theory_arith_nl.h (in part), and recast in cvc5 style. The interval
 * propagation, cross nested consistency, Groebner basis and nonlinear
 * branching procedures are not ported.
 */

#include "expr/node_manager.h"
#include "smt/env.h"
#include "z3/arith_util.h"
#include "z3/smt_context.h"
#include "z3/theory_arith.h"

namespace cvc5::internal {
namespace z3 {

/**
 * Return the value of v as a rational. If computedEpsilon = false and v has
 * an infinitesimal, then computeEpsilon() is invoked.
 */
TheoryArith::Numeral TheoryArith::getValue(TheoryVar v, bool& computedEpsilon)
{
  const InfNumeral& val = getValue(v);
  if (!val.getInfinitesimal().isZero() && !computedEpsilon)
  {
    computeEpsilon();
    refineEpsilon();
    computedEpsilon = true;
    d_modelDependsOnComputedEpsilon = true;
  }
  return val.getRational() + d_epsilon * val.getInfinitesimal();
}

/**
 * Return true if for the monomial x_1 * ... * x_n associated with v, the
 * following holds:
 *
 * getValue(x_1) * ... * getValue(x_n) = getValue(v)
 */
bool TheoryArith::checkMonomialAssignment(TheoryVar v, bool& computedEpsilon)
{
  Assert(isPureMonomial(var2expr(v)));
  TNode m = var2expr(v);
  Rational val(1), vVal;
  for (TNode arg : m)
  {
    TheoryVar curr = expr2var(arg);
    Assert(curr != s_nullTheoryVar);
    vVal = getValue(curr, computedEpsilon);
    val *= vVal;
  }
  vVal = getValue(v, computedEpsilon);
  Trace("z3-arith") << "v" << v << " := " << vVal << " == " << val << std::endl;
  return vVal == val;
}

/**
 * Return true if for every monomial x_1 * ... * x_n,
 * getValue(x_1) * ... * getValue(x_n) = getValue(x_1 * ... * x_n)
 */
bool TheoryArith::checkMonomialAssignments()
{
  bool computedEpsilon = false;
  for (TheoryVar v : d_nlMonomials)
  {
    if (d_ctx.isRelevant(getENode(v))
        && !checkMonomialAssignment(v, computedEpsilon))
    {
      return false;
    }
  }
  return true;
}

/** Return true if the given monomial is linear. */
bool TheoryArith::isMonomialLinear(TNode m) const
{
  Assert(isPureMonomial(m));
  size_t numNlVars = 0;
  for (TNode arg : m)
  {
    if (!d_ctx.eInternalized(arg))
    {
      return false;
    }
    TheoryVar var = expr2var(arg);
    if (!isFixed(var))
    {
      numNlVars++;
    }
    else if (lowerBound(var).isZero())
    {
      return true;
    }
  }
  return numNlVars <= 1;
}

/**
 * Return the product of the value of the fixed variables in the monomial m.
 */
TheoryArith::Numeral TheoryArith::getMonomialFixedVarProduct(TNode m) const
{
  Assert(isPureMonomial(m));
  Numeral r(1);
  for (TNode arg : m)
  {
    TheoryVar var = expr2var(arg);
    if (isFixed(var))
    {
      r *= lowerBound(var).getRational();
    }
  }
  return r;
}

/**
 * Return the first non fixed variable in the given monomial. Return null, if
 * the monomial does not have a non fixed variable.
 */
TNode TheoryArith::getMonomialNonFixedVar(TNode m) const
{
  Assert(isPureMonomial(m));
  for (TNode arg : m)
  {
    if (!isFixed(expr2var(arg)))
    {
      return arg;
    }
  }
  return TNode::null();
}

/**
 * Propagate linear monomial. Check whether the given monomial became linear
 * and propagate.
 */
bool TheoryArith::propagateLinearMonomial(TheoryVar v)
{
  if (d_data[v].d_nlPropagated)
  {
    return false;  // already propagated this monomial.
  }
  TNode m = var2expr(v);
  if (!isMonomialLinear(m))
  {
    return false;  // monomial is not linear.
  }

  d_stats.d_nlLinear++;

  d_data[v].d_nlPropagated = true;
  d_nlPropagated.push_back(v);
  Trace("z3-arith") << "v" << v << " is linear " << m << std::endl;

  Numeral k = getMonomialFixedVarProduct(m);
  TNode xN = k.isZero() ? TNode::null() : getMonomialNonFixedVar(m);
  DerivedBound* newLower = nullptr;
  DerivedBound* newUpper = nullptr;
  if (!xN.isNull())
  {
    // All but one of the x_i variables are assigned.
    // Let x_n be the unassigned variable.
    // Then, we know that x_1*...*x_n = k*x_n, where k is the product of
    // beta(x_1)*...*beta(x_{n-1}), beta(x_i) == lower(x_i)

    // Let m be (* x_1 ... x_n), then assert equality
    // (= (+ (* x_1 ... x_n) (* -k x_n)) 0) when x_1 ... x_{n-1} are fixed
    // variables, where k = lower(x_1)*...*lower(x_{n-1})
    k = -k;
    NodeManager* nm = d_ctx.getEnv().getNodeManager();
    // Z3 builds these terms without rewriting them; so does the port.
    Node kXN = k.isOne()
                   ? Node(xN)
                   : arith::mkMul(nm, arith::mkNumeral(nm, k, isInt(v)), xN);
    Node rhs = arith::mkAdd(nm, m, kXN);
    if (!hasVar(rhs))
    {
      d_ctx.internalize(rhs, false);
      d_ctx.markAsRelevant(rhs);
    }

    TheoryVar newV = expr2var(rhs);
    Assert(newV != s_nullTheoryVar);
    newLower = new DerivedBound(newV, InfNumeral(Rational(0)), B_LOWER);
    newUpper = new DerivedBound(newV, InfNumeral(Rational(0)), B_UPPER);
  }
  else
  {
    // One of the x_i variables is zero, or all of them are assigned.

    // Assert the equality
    // (= (* x_1 ... x_n) k)
    newLower = new DerivedBound(v, InfNumeral(k), B_LOWER);
    newUpper = new DerivedBound(v, InfNumeral(k), B_UPPER);
  }
  Assert(newLower != nullptr);
  Assert(newUpper != nullptr);
  d_boundsToDelete.push_back(newLower);
  d_assertedBounds.push_back(newLower);
  d_boundsToDelete.push_back(newUpper);
  d_assertedBounds.push_back(newUpper);

  // Add the justification for newLower and newUpper.
  // The justification is the lower and upper bounds of all fixed variables.
  d_tmpLitSet.clear();
  d_tmpEqSet.clear();

  Assert(isPureMonomial(m));
  bool foundZero = false;
  for (size_t i = 0; !foundZero && i < m.getNumChildren(); ++i)
  {
    TNode arg = m[i];
    TheoryVar var = expr2var(arg);
    if (isFixed(var))
    {
      Bound* l = lower(var);
      Bound* u = upper(var);
      if (l->getValue().isZero())
      {
        // if zero was found, then it is the explanation
        Assert(k.isZero());
        foundZero = true;
        d_tmpLitSet.clear();
        d_tmpEqSet.clear();
        newLower->d_lits.clear();
        newLower->d_eqs.clear();
      }
      accumulateJustification(
          *l, *newLower, Rational(0), d_tmpLitSet, d_tmpEqSet);
      accumulateJustification(
          *u, *newLower, Rational(0), d_tmpLitSet, d_tmpEqSet);
    }
  }
  newUpper->d_lits.insert(
      newUpper->d_lits.end(), newLower->d_lits.begin(), newLower->d_lits.end());
  newUpper->d_eqs.insert(
      newUpper->d_eqs.end(), newLower->d_eqs.begin(), newLower->d_eqs.end());

  return true;
}

/**
 * Traverse all non linear monomials, and check the ones that became linear
 * and propagate. Return true if propagated.
 */
bool TheoryArith::propagateLinearMonomials()
{
  if (!d_params.d_nlArithPropagateLinearMonomials)
  {
    return false;
  }
  if (!reflectionEnabled())
  {
    return false;
  }
  bool p = false;
  // CMW: d_nlMonomials can grow during this loop, so don't use iterators.
  for (size_t i = 0; i < d_nlMonomials.size(); ++i)
  {
    if (propagateLinearMonomial(d_nlMonomials[i]))
    {
      p = true;
    }
  }
  return p;
}

/** A monomial is 'pure' if it does not have a numeric coefficient. */
bool TheoryArith::isPureMonomial(TNode mon) const
{
  if (!arith::isMul(mon))
  {
    return false;
  }
  for (TNode arg : mon)
  {
    if (arith::isNumeral(arg) || arith::isMul(arg))
    {
      return false;
    }
  }
  return true;
}

/** Process non linear constraints. */
FinalCheckStatus TheoryArith::processNonLinear()
{
  d_modelDependsOnComputedEpsilon = false;
  if (d_nlMonomials.empty())
  {
    return FC_DONE;
  }

  if (!reflectionEnabled())
  {
    return FC_GIVEUP;
  }

  if (checkMonomialAssignments())
  {
    return FC_DONE;
  }

  if (!d_params.d_arithNl)
  {
    Trace("z3-arith") << "Non-linear is not enabled" << std::endl;
    return FC_GIVEUP;
  }

  // Not ported: the rest of Z3's process_non_linear (the d_nlRounds limit
  // d_params.d_nlArithRounds, elim_quasi_base_rows,
  // move_non_base_vars_to_bounds, max_min_nl_vars, and the interval
  // propagation, cross nested consistency, Groebner basis and nonlinear
  // branching strategies) only runs with smt.arith.nl=true. Give up instead.
  return FC_GIVEUP;
}

}  // namespace z3
}  // namespace cvc5::internal
