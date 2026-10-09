/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Integrality of the simplex-based arithmetic solver of the ported Z3 core:
 * GCD tests, patching, branch and bound and Gomory cuts.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), file
 * src/smt/theory_arith_int.h, and recast in cvc5 style.
 */

#include "expr/node_manager.h"
#include "smt/env.h"
#include "z3/arith_util.h"
#include "z3/clause.h"
#include "z3/justification.h"
#include "z3/smt_context.h"
#include "z3/theory_arith.h"

namespace cvc5::internal {
namespace z3 {

// -----------------------------------
//
// Integrality
//
// -----------------------------------

/**
 * Move non base variables to one of its bounds. If the variable does not have
 * bounds, it is integer, but it is not assigned to an integer value, then the
 * variable is set to an integer value. In mixed integer/real problems moving
 * a real variable to a bound could cause an integer value to have an
 * infinitesimal. Such an assignment would disable mkGomoryCut, and Z3 would
 * loop.
 */
void TheoryArith::moveNonBaseVarsToBounds()
{
  TheoryVar num = static_cast<TheoryVar>(getNumVars());
  for (TheoryVar v = 0; v < num; ++v)
  {
    if (isNonBase(v))
    {
      Bound* l = lower(v);
      Bound* u = upper(v);
      const InfNumeral& val = getValue(v);
      if (l != nullptr && u != nullptr)
      {
        if (val != l->getValue() && val != u->getValue())
        {
          setValue(v, l->getValue());
        }
      }
      else if (l != nullptr)
      {
        if (val != l->getValue())
        {
          setValue(v, l->getValue());
        }
      }
      else if (u != nullptr)
      {
        if (val != u->getValue())
        {
          setValue(v, u->getValue());
        }
      }
      else
      {
        if (isInt(v) && !val.isInt())
        {
          InfNumeral newVal(floor(val));
          setValue(v, newVal);
        }
      }
    }
  }
}

/**
 * Returns true if the there is an integer variable that is not assigned to an
 * integer value.
 */
bool TheoryArith::hasInfeasibleIntVar()
{
  int num = static_cast<int>(getNumVars());
  for (TheoryVar v = 0; v < num; ++v)
  {
    if (isInt(v) && !getValue(v).isInt())
    {
      return true;
    }
  }
  return false;
}

/**
 * Find an integer base var that is not assigned to an integer value, but is
 * bounded (i.e., it has lower and upper bounds). Return s_nullTheoryVar if
 * all integer base variables are assigned to integer values.
 *
 * If there are multiple variables satisfying the condition above, then select
 * the one with the tightest bound.
 */
TheoryVar TheoryArith::findBoundedInfeasibleIntBaseVar()
{
  TheoryVar result = s_nullTheoryVar;
  Numeral range;
  Numeral newRange;
  Numeral smallRangeThreshold(1024);
  unsigned n = 0;
  for (const Row& row : d_rows)
  {
    TheoryVar v = row.getBaseVar();
    if (v == s_nullTheoryVar)
    {
      continue;
    }
    if (!isBase(v))
    {
      continue;
    }
    if (!isInt(v))
    {
      continue;
    }
    if (getValue(v).isInt())
    {
      continue;
    }
    if (!isBounded(v))
    {
      continue;
    }
    const Numeral& l = lowerBound(v).getRational();
    const Numeral& u = upperBound(v).getRational();
    newRange = u;
    newRange -= l;
    if (newRange > smallRangeThreshold)
    {
      //
    }
    else if (result == s_nullTheoryVar || newRange < range)
    {
      result = v;
      range = newRange;
      n = 1;
    }
    else if (newRange == range)
    {
      n++;
      if (static_cast<unsigned>(d_random()) % n == 0)
      {
        result = v;
        range = newRange;
      }
    }
  }
  return result;
}

/**
 * Find an integer base var that is not assigned to an integer value. Return
 * s_nullTheoryVar if all integer base variables are assigned to integer
 * values.
 *
 * This method gives preference to bounded integer variables. If all
 * variables are unbounded, then it selects a random one.
 */
TheoryVar TheoryArith::findInfeasibleIntBaseVar()
{
  TheoryVar r = findBoundedInfeasibleIntBaseVar();

  unsigned n = 0;

  // Z3's SELECT_VAR macro
  auto selectVar = [&](TheoryVar var) {
    if (r == s_nullTheoryVar)
    {
      n = 1;
      r = var;
    }
    else
    {
      n++;
      Assert(n >= 2);
      if (static_cast<unsigned>(d_random()) % n == 0)
      {
        r = var;
      }
    }
  };

  Numeral smallValue(1024);
  if (r == s_nullTheoryVar)
  {
    for (const Row& row : d_rows)
    {
      TheoryVar v = row.getBaseVar();
      if (v != s_nullTheoryVar && isBase(v) && isInt(v) && !getValue(v).isInt())
      {
        if (abs(getValue(v)) < smallValue)
        {
          selectVar(v);
        }
        else if (upper(v) && smallValue > upperBound(v) - getValue(v))
        {
          selectVar(v);
        }
        else if (lower(v) && smallValue > getValue(v) - lowerBound(v))
        {
          selectVar(v);
        }
      }
    }
  }

  if (r == s_nullTheoryVar)
  {
    for (const Row& row : d_rows)
    {
      TheoryVar v = row.getBaseVar();
      if (v != s_nullTheoryVar && isBase(v) && isInt(v) && !getValue(v).isInt())
      {
        selectVar(v);
      }
    }
  }

  if (r == s_nullTheoryVar)
  {
    // Z3 iterates m_rows with a range-based for loop, whose end is computed
    // once; the index-based loop below has the same bound.
    size_t numRows = d_rows.size();
    for (size_t i = 0; i < numRows; ++i)
    {
      TheoryVar v = d_rows[i].getBaseVar();
      if (v != s_nullTheoryVar && isQuasiBase(v) && isInt(v)
          && !getValue(v).isInt())
      {
        quasiBaseRow2BaseRow(getVarRow(v));
        selectVar(v);
      }
    }
  }
  return r;
}

/**
 * Create "branch and bound" case-split.
 */
void TheoryArith::branchInfeasibleIntVar(TheoryVar v)
{
  Assert(isInt(v));
  Assert(!getValue(v).isInt());
  NodeManager* nm = d_ctx.getEnv().getNodeManager();
  d_stats.d_branches++;
  Numeral k = ceil(getValue(v));
  Trace("z3-arith") << "branching v" << v << " = " << getValue(v)
                    << ", k = " << k << std::endl;
  Node e = getENode(v)->getExpr();
  Node bound = arith::mkGe(nm, e, arith::mkNumeral(nm, k, arith::isIntSort(e)));
  {
    d_ctx.internalize(bound, true);
    d_ctx.markAsRelevant(bound);
  }
}

/**
 * Create a "cut from proof" lemma.
 *
 * The set of rows where the base variable is tight are extracted. These row
 * equalities are checked for integer feasiability. If they are not integer
 * feasible, then an integer infeasible equation, that is implied from the
 * extracted equalities is extracted. The extracted equality a*x = 0 is
 * blocked by asserting the disjunction (a*x > 0 \/ a*x < 0)
 */
bool TheoryArith::branchInfeasibleIntEquality()
{
  // Not ported: Z3 solves the extracted equalities with arith_eq_solver
  // (solve_integer_equations), which is only reached when
  // m_arith_int_eq_branching is set (default false). Report that the
  // equalities were integer feasible, as solve_integer_equations does when
  // it finds no witness.
  return false;
}

/**
 * Create bounds for (non base) free vars in the given row. Return true if at
 * least one variable was constrained. This method is used to enable the
 * application of gomory cuts.
 */
bool TheoryArith::constrainFreeVars(const Row& r)
{
  bool result = false;
  TheoryVar b = r.getBaseVar();
  Assert(b != s_nullTheoryVar);
  NodeManager* nm = d_ctx.getEnv().getNodeManager();
  std::vector<RowEntry>::const_iterator it = r.begin();
  std::vector<RowEntry>::const_iterator end = r.end();
  for (; it != end; ++it)
  {
    if (!it->isDead() && it->d_var != b && isFree(it->d_var))
    {
      TheoryVar v = it->d_var;
      Node e = getENode(v)->getExpr();
      bool eIsInt = arith::isIntSort(e);
      Node bound =
          arith::mkGe(nm, e, arith::mkNumeral(nm, Rational(0), eIsInt));
      {
        d_ctx.internalize(bound, true);
      }
      d_ctx.markAsRelevant(bound);
      result = true;
    }
  }
  return result;
}

/**
 * Return true if it is possible to apply a gomory cut on the given row.
 *
 * See constrainFreeVars.
 */
bool TheoryArith::isGomoryCutTarget(const Row& r)
{
  TheoryVar b = r.getBaseVar();
  for (const RowEntry& e : r)
  {
    // All non base variables must be at their bounds and assigned to
    // rationals (that is, infinitesimals are not allowed).
    if (!e.isDead() && e.d_var != b
        && (!atBound(e.d_var) || !getValue(e.d_var).isRational()))
    {
      return false;
    }
  }
  return true;
}

Node TheoryArith::mkPolynomialGe(size_t numArgs,
                                 const RowEntry* args,
                                 const Rational& k)
{
  // Remark: the polynomials internalized by theory_arith may not satisfy
  // poly_simplifier_plugin->wf_polynomial assertion.
  bool allInt = true;
  for (size_t i = 0; i < numArgs && allInt; ++i)
  {
    allInt = isInt(args[i].d_var);
  }

  NodeManager* nm = d_ctx.getEnv().getNodeManager();
  std::vector<Node> pargs;

  for (size_t i = 0; i < numArgs; ++i)
  {
    const Rational& ck = args[i].d_coeff;
    Node x = getENode(args[i].d_var)->getExpr();
    if (arith::isIntSort(x) && !allInt)
    {
      x = nm->mkNode(Kind::TO_REAL, x);
    }
    if (ck.isOne())
    {
      pargs.push_back(x);
    }
    else
    {
      pargs.push_back(
          arith::mkMul(nm, arith::mkNumeral(nm, ck, arith::isIntSort(x)), x));
    }
  }

  // m_util.mk_add(n, args) returns the argument itself when n == 1
  Node pol = pargs.size() == 1 ? pargs[0] : nm->mkNode(Kind::ADD, pargs);
  Node result = arith::mkGe(nm, pol, arith::mkNumeral(nm, k, allInt));
  result = d_ctx.rewriteInstance(result);
  return result;
}

/**
 * gomory_cut_justification. Remark: the assignment must be propagated back to
 * arith, hence the null "from theory".
 */
class TheoryArith::GomoryCutJustification
    : public ExtTheoryPropagationJustification
{
 public:
  GomoryCutJustification(TheoryId fid,
                         SmtContext& ctx,
                         size_t numLits,
                         const Literal* lits,
                         size_t numEqs,
                         const ENodePair* eqs,
                         Antecedents& /*bounds*/,
                         Literal consequent)
      : ExtTheoryPropagationJustification(
            fid, ctx, numLits, lits, numEqs, eqs, consequent)
  {
  }
  TheoryId getFromTheory() const override { return s_nullTheoryId; }
};

/**
 * Create a gomory cut for the given row.
 */
bool TheoryArith::mkGomoryCut(const Row& r)
{
  // The following assertion is wrong. It may be violated in mixed-integer
  // problems.
  // Assert(!allCoeffInt(r));
  TheoryVar xI = r.getBaseVar();

  Assert(isInt(xI));
  // The following assertion is wrong. It may be violated in
  // mixed-real-integer problems. The check isGomoryCutTarget will discard
  // rows where any variable contains infinitesimals.
  // Assert(d_value[xI].isRational());
  // the base variable is not assigned to an integer value.
  Assert(!d_value[xI].isInt());

  bool cfv = constrainFreeVars(r);

  if (cfv || !isGomoryCutTarget(r))
  {
    return false;
  }

  Antecedents ante(*this);

  d_stats.d_gomoryCuts++;

  // gomory will be   pol >= k
  Numeral k(1);
  std::vector<RowEntry> pol;

  Numeral f0 = fractionalPart(d_value[xI]);
  Numeral oneMinusF0 = Numeral(1) - f0;
  Assert(!f0.isZero());
  Assert(!oneMinusF0.isZero());

  Numeral lcmDen(1);
  unsigned numInts = 0;

  for (const RowEntry& e : r)
  {
    if (!e.isDead() && e.d_var != xI)
    {
      TheoryVar xJ = e.d_var;
      Numeral aIJ = e.d_coeff;
      // make the used format compatible with the format used in: Integrating
      // Simplex with DPLL(T)
      aIJ = -aIJ;
      if (isReal(xJ))
      {
        Numeral newAIJ;
        if (atLower(xJ))
        {
          if (isPos(aIJ))
          {
            newAIJ = aIJ / oneMinusF0;
          }
          else
          {
            newAIJ = aIJ / f0;
            newAIJ = -newAIJ;
          }
          k += newAIJ * lowerBound(xJ).getRational();
          lower(xJ)->pushJustification(ante, newAIJ, coeffsEnabled());
        }
        else
        {
          Assert(atUpper(xJ));
          if (isPos(aIJ))
          {
            newAIJ = aIJ / f0;
            newAIJ = -newAIJ;  // the upper terms are inverted.
          }
          else
          {
            newAIJ = aIJ / oneMinusF0;
          }
          k += newAIJ * upperBound(xJ).getRational();
          upper(xJ)->pushJustification(ante, newAIJ, coeffsEnabled());
        }
        pol.push_back(RowEntry(newAIJ, xJ));
      }
      else
      {
        ++numInts;
        Assert(isInt(xJ));
        Numeral fJ = fractionalPart(aIJ);
        if (!fJ.isZero())
        {
          Numeral newAIJ;
          if (atLower(xJ))
          {
            if (fJ <= oneMinusF0)
            {
              newAIJ = fJ / oneMinusF0;
            }
            else
            {
              newAIJ = (Numeral(1) - fJ) / f0;
            }
            k += newAIJ * lowerBound(xJ).getRational();
            lower(xJ)->pushJustification(ante, newAIJ, coeffsEnabled());
          }
          else
          {
            Assert(atUpper(xJ));
            if (fJ <= f0)
            {
              newAIJ = fJ / f0;
            }
            else
            {
              newAIJ = (Numeral(1) - fJ) / oneMinusF0;
            }
            newAIJ = -newAIJ;  // the upper terms are inverted
            k += newAIJ * upperBound(xJ).getRational();
            upper(xJ)->pushJustification(ante, newAIJ, coeffsEnabled());
          }
          pol.push_back(RowEntry(newAIJ, xJ));
          lcmDen = lcm(lcmDen, denominator(newAIJ));
        }
      }
    }
  }

  NodeManager* nm = d_ctx.getEnv().getNodeManager();
  Node bound;
  if (pol.empty())
  {
    if (ante.lits().empty() && ante.eqs().empty())
    {
      return false;
    }
    Assert(isPos(k));
    // conflict 0 >= k where k is positive
    setConflict(ante, ante, "gomory-cut");
    return true;
  }
  else if (pol.size() == 1)
  {
    TheoryVar v = pol[0].d_var;
    k /= pol[0].d_coeff;
    bool isLower = isPos(pol[0].d_coeff);
    if (isInt(v) && !k.isIntegral())
    {
      k = isLower ? ceil(k) : floor(k);
    }
    if (isLower)
    {
      bound = arith::mkGe(
          nm, getENode(v)->getExpr(), arith::mkNumeral(nm, k, isInt(v)));
    }
    else
    {
      bound = arith::mkLe(
          nm, getENode(v)->getExpr(), arith::mkNumeral(nm, k, isInt(v)));
    }
  }
  else
  {
    if (numInts > 0)
    {
      lcmDen = lcm(lcmDen, denominator(k));
      Assert(isPos(lcmDen));
      if (!lcmDen.isOne())
      {
        // normalize coefficients of integer parameters to be integers.
        size_t n = pol.size();
        for (size_t i = 0; i < n; ++i)
        {
          pol[i].d_coeff *= lcmDen;
          Assert(!isInt(pol[i].d_var) || pol[i].d_coeff.isIntegral());
        }
        k *= lcmDen;
      }
    }
    bound = mkPolynomialGe(pol.size(), pol.data(), k);
  }
  Trace("z3-arith") << "new cut: " << bound << std::endl;
  Literal l = s_nullLiteral;
  {
    d_ctx.internalize(bound, true);
  }
  l = d_ctx.getLiteral(bound);
  d_ctx.markAsRelevant(l);
  Justification* js =
      d_ctx.mkJustification(GomoryCutJustification(getId(),
                                                   d_ctx,
                                                   ante.lits().size(),
                                                   ante.lits().data(),
                                                   ante.eqs().size(),
                                                   ante.eqs().data(),
                                                   ante,
                                                   l));

  if (l == s_falseLiteral)
  {
    d_ctx.mkClause(0, nullptr, js, CLS_TH_LEMMA, nullptr);
  }
  else
  {
    d_ctx.assign(l, js);
  }
  return true;
}

/**
 * Return false if the row failed the GCD test, that is, a conflict was
 * detected.
 *
 * If the variables with the least coefficient are bounded, then the
 * extGcdTest is invoked.
 */
bool TheoryArith::gcdTest(const Row& r)
{
  if (!d_params.d_arithGcdTest)
  {
    return true;
  }
  d_stats.d_gcdTests++;
  Numeral lcmDen = r.getDenominatorsLcm();
  Numeral consts(0);
  Numeral gcds(0);
  Numeral leastCoeff(0);
  bool leastCoeffIsBounded = false;
  for (const RowEntry& e : r)
  {
    if (!e.isDead())
    {
      if (isFixed(e.d_var))
      {
        // WARNING: it is not safe to use getValue(e.d_var) here, since
        // getValue(e.d_var) may not satisfy e.d_var bounds at this point.
        Numeral aux = lcmDen * e.d_coeff;
        consts += aux * lowerBound(e.d_var).getRational();
      }
      else if (isReal(e.d_var))
      {
        return true;
      }
      else if (gcds.isZero())
      {
        gcds = abs(lcmDen * e.d_coeff);
        leastCoeff = gcds;
        leastCoeffIsBounded = isBounded(e.d_var);
      }
      else
      {
        Numeral aux = abs(lcmDen * e.d_coeff);
        gcds = gcd(gcds, aux);
        if (aux < leastCoeff)
        {
          leastCoeff = aux;
          leastCoeffIsBounded = isBounded(e.d_var);
        }
        else if (leastCoeffIsBounded && aux == leastCoeff)
        {
          leastCoeffIsBounded = isBounded(e.d_var);
        }
      }
      Assert(gcds.isIntegral());
      Assert(leastCoeff.isIntegral());
    }
  }

  if (gcds.isZero())
  {
    // All variables are fixed.
    // This theory guarantees that the assignment satisfies each row, and
    // fixed integer variables are assigned to integer values.
    return true;
  }

  if (!(consts / gcds).isIntegral())
  {
    Antecedents ante(*this);
    d_stats.d_gcdConflicts++;
    collectFixedVarJustifications(r, ante);
    d_ctx.setConflict(d_ctx.mkJustification(
        ExtTheoryConflictJustification(getId(),
                                       d_ctx,
                                       ante.lits().size(),
                                       ante.lits().data(),
                                       ante.eqs().size(),
                                       ante.eqs().data())));
    return false;
  }

  if (leastCoeff.isOne() && !leastCoeffIsBounded)
  {
    Assert(gcds.isOne());
    return true;
  }

  if (leastCoeffIsBounded)
  {
    return extGcdTest(r, leastCoeff, lcmDen, consts);
  }
  return true;
}

/**
 * Auxiliary method for gcdTest.
 */
bool TheoryArith::extGcdTest(const Row& r,
                             const Numeral& leastCoeff,
                             const Numeral& lcmDen,
                             const Numeral& consts)
{
  Numeral gcds(0);
  Numeral l(consts);
  Numeral u(consts);

  Antecedents ante(*this);

  for (const RowEntry& e : r)
  {
    if (!e.isDead() && !isFixed(e.d_var))
    {
      TheoryVar v = e.d_var;
      Assert(!isReal(v));
      Numeral ncoeff = lcmDen * e.d_coeff;
      Assert(ncoeff.isIntegral());
      Numeral absNcoeff = abs(ncoeff);
      if (absNcoeff == leastCoeff)
      {
        Assert(isBounded(v));
        if (isPos(ncoeff))
        {
          // l += ncoeff * lowerBound(v).getRational();
          l += ncoeff * lowerBound(v).getRational();
          // u += ncoeff * upperBound(v).getRational();
          u += ncoeff * upperBound(v).getRational();
        }
        else
        {
          // l += ncoeff * upperBound(v).getRational();
          l += ncoeff * upperBound(v).getRational();
          // u += ncoeff * lowerBound(v).getRational();
          u += ncoeff * lowerBound(v).getRational();
        }
        lower(v)->pushJustification(ante, e.d_coeff, coeffsEnabled());
        upper(v)->pushJustification(ante, e.d_coeff, coeffsEnabled());
      }
      else if (gcds.isZero())
      {
        gcds = absNcoeff;
      }
      else
      {
        gcds = gcd(gcds, absNcoeff);
      }
      Assert(gcds.isIntegral());
    }
  }

  if (gcds.isZero())
  {
    return true;
  }

  Numeral l1 = ceil(l / gcds);
  Numeral u1 = floor(u / gcds);

  if (u1 < l1)
  {
    d_stats.d_gcdConflicts++;
    collectFixedVarJustifications(r, ante);
    d_ctx.setConflict(d_ctx.mkJustification(
        ExtTheoryConflictJustification(getId(),
                                       d_ctx,
                                       ante.lits().size(),
                                       ante.lits().data(),
                                       ante.eqs().size(),
                                       ante.eqs().data())));
    return false;
  }

  return true;
}

/**
 * Return true if all rows pass the GCD test.
 */
bool TheoryArith::gcdTest()
{
  if (!d_params.d_arithGcdTest)
  {
    return true;
  }
  if (d_eagerGcd)
  {
    return true;
  }
  for (const Row& e : d_rows)
  {
    TheoryVar v = e.getBaseVar();
    if (v != s_nullTheoryVar && isInt(v) && !getValue(v).isInt() && !gcdTest(e))
    {
      if (d_params.d_arithAdaptiveGcd)
      {
        d_eagerGcd = true;
      }
      return false;
    }
  }
  return true;
}

/**
 * Try to create bounds for unbounded infeasible integer variables. Return
 * false if an inconsistency is detected.
 */
bool TheoryArith::maxMinInfeasibleIntVars()
{
  VarSet& alreadyProcessed = d_tmpVarSet;
  alreadyProcessed.clear();
  std::vector<TheoryVar> vars;
  for (;;)
  {
    vars.clear();
    // Collect infeasible integer variables.
    for (const Row& e : d_rows)
    {
      TheoryVar v = e.getBaseVar();
      if (v != s_nullTheoryVar && isInt(v) && !getValue(v).isInt()
          && !isBounded(v)
          && alreadyProcessed.find(v) == alreadyProcessed.end())
      {
        vars.push_back(v);
        alreadyProcessed.insert(v);
      }
    }
    if (vars.empty())
    {
      return true;
    }
    if (maxMin(vars))
    {
      return false;
    }
  }
}

/**
 * Try to patch int infeasible vars using freedom intervals.
 */
void TheoryArith::patchIntInfeasibleVars()
{
  Assert(d_toPatch.empty());
  int num = static_cast<int>(getNumVars());
  bool infL, infU;
  InfNumeral l, u;
  Numeral m;
  for (TheoryVar v = 0; v < num; ++v)
  {
    if (!isNonBase(v))
    {
      continue;
    }
    getFreedomInterval(v, infL, l, infU, u, m);
    if (m.isOne() && getValue(v).isInt())
    {
      continue;
    }
    // check whether value of v is already a multiple of m.
    if ((getValue(v).getRational() / m).isIntegral())
    {
      continue;
    }
    if (!infL)
    {
      l = ceil(l);
    }
    if (!infU)
    {
      u = floor(u);
    }
    if (!m.isOne())
    {
      if (!infL)
      {
        l = m * ceil(l / m);
      }
      if (!infU)
      {
        u = m * floor(u / m);
      }
    }
    if (!infL && !infU && l > u)
    {
      continue;  // cannot patch
    }
    if (!infL)
    {
      setValue(v, l);
    }
    else if (!infU)
    {
      setValue(v, u);
    }
    else
    {
      setValue(v, InfNumeral(0));
    }
  }
  Assert(d_toPatch.empty());
}

/**
 * Force all non basic variables to be assigned to integer values.
 */
void TheoryArith::fixNonBaseVars()
{
  int num = static_cast<int>(getNumVars());
  for (TheoryVar v = 0; v < num; ++v)
  {
    if (!isNonBase(v))
    {
      continue;
    }
    if (!isInt(v))
    {
      continue;
    }
    if (getValue(v).isInt())
    {
      continue;
    }
    InfNumeral newVal(floor(getValue(v)));
    setValue(v, newVal);
  }
  if (!makeFeasible())
  {
    failed();
  }
}

/**
 * Return FC_DONE if the assignment is int feasible. Otherwise, apply GCD
 * test, branch and bound and Gomory Cuts.
 */
FinalCheckStatus TheoryArith::checkIntFeasibility()
{
  if (!hasInfeasibleIntVar())
  {
    return FC_DONE;
  }

  if (d_params.d_arithIgnoreInt)
  {
    return FC_GIVEUP;
  }

  if (!gcdTest())
  {
    return FC_CONTINUE;
  }

  if (d_ctx.inconsistent())
  {
    return FC_CONTINUE;
  }

  removeFixedVarsFromBase();

  d_stats.d_patches++;
  patchIntInfeasibleVars();
  fixNonBaseVars();

  if (d_ctx.inconsistent())
  {
    return FC_CONTINUE;
  }

  TheoryVar intVar = findInfeasibleIntBaseVar();
  if (intVar == s_nullTheoryVar)
  {
    d_stats.d_patchesSucc++;
    return d_liberalFinalCheck || !d_changedAssignment ? FC_DONE : FC_CONTINUE;
  }

  // Z3 has a disabled (#if 0) block here that calls maxMinInfeasibleIntVars
  // and gcdTest when findBoundedInfeasibleIntBaseVar finds nothing.

  d_branchCutCounter++;
  // TODO: add giveup code
  if (d_branchCutCounter % d_params.d_arithBranchCutRatio == 0)
  {
    moveNonBaseVarsToBounds();
    if (!makeFeasible())
    {
      failed();
      return FC_CONTINUE;
    }
    TheoryVar intVar2 = findInfeasibleIntBaseVar();
    if (intVar2 != s_nullTheoryVar)
    {
      Assert(isBase(intVar2));
      const Row& r = d_rows[getVarRow(intVar2)];
      if (!mkGomoryCut(r))
      {
        Trace("z3-arith") << "gomory cut: silent failure" << std::endl;
      }
      return FC_CONTINUE;
    }
  }
  else
  {
    if (d_params.d_arithIntEqBranching && branchInfeasibleIntEquality())
    {
      ++d_stats.d_branchInfeasibleInt;
      return FC_CONTINUE;
    }

    TheoryVar intVar2 = findInfeasibleIntBaseVar();
    if (intVar2 != s_nullTheoryVar)
    {
      // apply branching
      branchInfeasibleIntVar(intVar2);
      ++d_stats.d_branchInfeasibleVar;
      return FC_CONTINUE;
    }
  }
  return d_liberalFinalCheck || !d_changedAssignment ? FC_DONE : FC_CONTINUE;
}

}  // namespace z3
}  // namespace cvc5::internal
