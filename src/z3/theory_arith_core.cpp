/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The core of the simplex-based arithmetic solver of the ported Z3 core:
 * internalization, bound axioms, the simplex (pivoting, make feasible),
 * bound assertion and propagation, conflicts and backtracking.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), file
 * src/smt/theory_arith_core.h, and recast in cvc5 style.
 */

#include <algorithm>
#include <climits>
#include <map>
#include <unordered_set>

#include "base/exception.h"
#include "expr/node_manager.h"
#include "theory/theory.h"
#include "z3/arith_util.h"
#include "z3/ast.h"
#include "z3/justification.h"
#include "z3/smt_context.h"
#include "z3/theory_arith.h"
#include "z3/util/trail.h"

namespace cvc5::internal {
namespace z3 {

namespace {

/**
 * Not from Z3: true for an arithmetic-sorted uninterpreted constant. cvc5
 * attributes such a constant to arithmetic (type-based theoryOf), so the core
 * hands it to internalizeTerm; in Z3 it belongs to no family and is
 * internalized by the core as an uninterpreted term.
 */
bool isArithLeaf(TNode n)
{
  return n.getMetaKind() == kind::metakind::VARIABLE;
}

/** Z3's is_uninterp: an application of a user declared symbol. */
bool isUninterp(TNode n)
{
  return n.getMetaKind() == kind::metakind::VARIABLE
         || n.getKind() == Kind::APPLY_UF;
}

/** m_util.get_family_id() == n->get_family_id() */
bool isArithFamily(TNode n)
{
  return n.getMetaKind() != kind::metakind::VARIABLE
         && theory::kindToTheoryId(n.getKind()) == theory::THEORY_ARITH;
}

/** m_util.is_zero(n) */
bool isZero(TNode n)
{
  Rational val;
  return arith::isNumeral(n, val) && val.isZero();
}

}  // namespace

class TheoryArith::ScopedRowVars
{
 public:
  ScopedRowVars(std::vector<UIntSet>& rowVars, size_t& top) : d_top(top)
  {
    Assert(rowVars.size() >= top);
    if (rowVars.size() == top)
    {
      rowVars.push_back(UIntSet());
    }
    rowVars[top].reset();
    ++d_top;
  }
  ~ScopedRowVars() { --d_top; }

 private:
  size_t& d_top;
};

// ---------------------------------------------------------------------------

void TheoryArith::foundUnsupportedOp(TNode n)
{
  d_unsupportedOps.push_back(n);
  d_ctx.pushTrail(PushBackVector<std::vector<Node>>(d_unsupportedOps));
  // Not from Z3: this is how the port signals incompleteness, so that a sat
  // answer becomes unknown.
  d_ctx.markModelUnsound(getId());
}

void TheoryArith::foundUnderspecifiedOp(TNode n)
{
  d_underspecifiedOps.push_back(n);
  d_ctx.pushTrail(PushBackVector<std::vector<Node>>(d_underspecifiedOps));
  // Z3 also asserts n = div0(p, q) (resp. idiv0, mod0, rem0, power0), which
  // ties n to the function that interprets division by zero in the model.
  // cvc5 has no such symbols: the total operators have a fixed value at zero
  // (see mkTotalDivZeroAxiom), and the congruence of n itself is kept by the
  // E-graph since division is reflected.
}

bool TheoryArith::processAtoms() const
{
  if (!adaptive())
  {
    return true;
  }
  uint64_t totalConflicts = d_ctx.getNumConflicts();
  if (totalConflicts < 10)
  {
    return true;
  }
  double f = static_cast<double>(getNumConflicts())
             / static_cast<double>(totalConflicts);
  return f >= adaptiveAssertionThreshold();
}

bool TheoryArith::isIntExpr(TNode e)
{
  // m_util.is_int_expr(e)
  if (arith::isIntSort(e))
  {
    return true;
  }
  if (isUninterp(e))
  {
    return false;
  }
  std::vector<TNode> todo;
  todo.push_back(e);
  size_t i = 0;
  while (!todo.empty())
  {
    ++i;
    // IS_INT_EXPR_DEPTH_LIMIT
    if (i > 100)
    {
      return false;
    }
    e = todo.back();
    todo.pop_back();
    if (arith::isToReal(e))
    {
      // pass
    }
    else if (arith::isNumeral(e) && arith::isIntSort(e))
    {
      // pass
    }
    else if (arith::isAdd(e) || arith::isMul(e))
    {
      for (TNode arg : e)
      {
        todo.push_back(arg);
      }
    }
    else
    {
      return false;
    }
  }
  return true;
}

TheoryVar TheoryArith::mkVar(ENode* n)
{
  TheoryVar r = Theory::mkVar(n);
  Assert(r == static_cast<int>(d_columns.size()));
  bool isIntV = isIntExpr(n->getExpr());
  d_columns.push_back(Column());
  d_data.push_back(VarData(isIntV));
  if (randomInitialValue())
  {
    int val = (d_random() % (randomUpper() - randomLower())) + randomLower();
    d_value.push_back(InfNumeral(val));
  }
  else
  {
    d_value.push_back(InfNumeral());
  }
  d_oldValue.push_back(InfNumeral());
  Assert(d_varOccs.size() == static_cast<size_t>(r));
  d_varOccs.push_back(Atoms());
  d_unassignedAtoms.push_back(0);
  d_varPos.push_back(-1);
  d_bounds[0].push_back(nullptr);
  d_bounds[1].push_back(nullptr);
  if (r >= static_cast<int>(d_toPatch.getBounds()))
  {
    d_toPatch.setBounds(r + 1);
  }
  d_inUpdateTrailStack.assureDomain(r);
  d_leftBasis.assureDomain(r);
  d_inToCheck.assureDomain(r);
  if (isPureMonomial(n->getExpr()))
  {
    d_nlMonomials.push_back(r);
  }
  d_ctx.attachThVar(n, this, r);
  return r;
}

bool TheoryArith::reflectionEnabled() const { return d_params.d_arithReflect; }

bool TheoryArith::reflect(TNode n) const
{
  if (reflectionEnabled())
  {
    return true;  // reflect everything
  }
  // Every underspecified operator must be reflected in the egraph.
  switch (n.getKind())
  {
    case Kind::DIVISION:
    case Kind::DIVISION_TOTAL:
    case Kind::INTS_DIVISION:
    case Kind::INTS_DIVISION_TOTAL:
    case Kind::INTS_MODULUS:
    case Kind::INTS_MODULUS_TOTAL: return true;
    default: break;
  }
  return false;
}

bool TheoryArith::enableCgcFor(TNode n) const
{
  // Congruence closure is not enabled for (+ ...) and (* ...) applications.
  return !(arith::isAdd(n) || arith::isMul(n));
}

ENode* TheoryArith::mkENode(TNode n)
{
  if (d_ctx.eInternalized(n))
  {
    return d_ctx.getENode(n);
  }
  return d_ctx.mkENode(n, !reflect(n), false, enableCgcFor(n));
}

void TheoryArith::mkENodeIfReflect(TNode n)
{
  if (reflectionEnabled())
  {
    // make sure that n is in the e-graph
    mkENode(n);
  }
}

UIntSet& TheoryArith::rowVars()
{
  Assert(d_rowVarsTop > 0);
  return d_rowVars[d_rowVarsTop - 1];
}

template <bool invert>
void TheoryArith::addRowEntry(size_t rId, const Numeral& coeff, TheoryVar v)
{
  Row& r = d_rows[rId];
  Column& c = d_columns[v];
  if (rowVars().contains(v))
  {
    for (size_t rIdx = 0; rIdx < r.size(); ++rIdx)
    {
      RowEntry& re = r[rIdx];
      Assert(!re.isDead());
      if (re.d_var == v)
      {
        if (invert)
        {
          re.d_coeff -= coeff;
        }
        else
        {
          re.d_coeff += coeff;
        }
        if (re.d_coeff.isZero())
        {
          int cIdx = re.d_colIdx;
          r.delRowEntry(rIdx);
          c.delColEntry(cIdx);
          rowVars().remove(v);
          r.compress(d_columns);
          c.compress(d_rows);
        }
        return;
      }
    }
    Assert(false);
    return;
  }
  rowVars().insert(v);
  int rIdx;
  RowEntry& rEntry = r.addRowEntry(rIdx);
  int cIdx;
  ColEntry& cEntry = c.addColEntry(cIdx);

  rEntry.d_var = v;
  rEntry.d_coeff = coeff;
  if (invert)
  {
    rEntry.d_coeff = -rEntry.d_coeff;
  }
  rEntry.d_colIdx = cIdx;

  cEntry.d_rowId = static_cast<int>(rId);
  cEntry.d_rowIdx = rIdx;
  d_stats.d_tableauMaxColumns = std::max(d_stats.d_tableauMaxColumns,
                                         static_cast<uint64_t>(v) + 1);
}

void TheoryArith::internalizeInternalMonomial(TNode m, size_t rId)
{
  if (d_ctx.eInternalized(m))
  {
    ENode* e = d_ctx.getENode(m);
    if (isAttachedToVar(e))
    {
      // there is already a theory variable (i.e., name) for m.
      TheoryVar v = e->getThVar(getId());
      addRowEntry<false>(rId, Rational(-1), v);
      return;
    }
  }
  Rational val1, val2;
  if (arith::isMul(m) && m.getNumChildren() == 2
      && arith::isNumeral(m[0], val1) && isApp(m[0]) && isApp(m[1]))
  {
    TNode arg1 = m[0];
    TNode arg2 = m[1];
    if (arith::isNumeral(arg2, val2))
    {
      // Note: Z3 adds the two numerals here.
      Numeral val(val1 + val2);
      if (reflectionEnabled())
      {
        internalizeTermCore(arg1);
        internalizeTermCore(arg2);
        mkENode(m);
      }
      TheoryVar v = internalizeNumeral(m, val);
      addRowEntry<true>(rId, Rational(1), v);
      return;
    }
    Numeral val(val1);
    TheoryVar v = internalizeTermCore(arg2);
    if (reflectionEnabled())
    {
      internalizeTermCore(arg1);
      mkENode(m);
    }
    addRowEntry<true>(rId, val, v);
  }
  else
  {
    TheoryVar v = internalizeTermCore(m);
    addRowEntry<false>(rId, Rational(-1), v);
  }
}

void TheoryArith::checkApp(TNode e, TNode n)
{
  if (isApp(e))
  {
    return;
  }
  std::stringstream strm;
  strm << n << " contains a "
       << (isQuantifier(e) ? "quantifier" : "free variable");
  throw Exception(strm.str());
}

TheoryVar TheoryArith::internalizeSub(TNode n)
{
  Assert(arith::isSub(n));
  bool first = true;
  size_t rId = mkRow();
  ScopedRowVars sc(d_rowVars, d_rowVarsTop);
  TheoryVar v;
  for (TNode arg : n)
  {
    checkApp(arg, n);
    v = internalizeTermCore(arg);
    if (first)
    {
      addRowEntry<true>(rId, Rational(1), v);
    }
    else
    {
      addRowEntry<false>(rId, Rational(1), v);
    }
    first = false;
  }
  ENode* e = mkENode(n);
  v = e->getThVar(getId());
  if (v == s_nullTheoryVar)
  {
    v = mkVar(e);
    addRowEntry<false>(rId, Rational(1), v);
    initRow(rId);
  }
  else
  {
    delRow(rId);
  }
  return v;
}

TheoryVar TheoryArith::internalizeAdd(TNode n)
{
  Assert(arith::isAdd(n));
  size_t rId = mkRow();
  ScopedRowVars sc(d_rowVars, d_rowVarsTop);
  for (TNode arg : n)
  {
    checkApp(arg, n);
    internalizeInternalMonomial(arg, rId);
  }
  ENode* e = mkENode(n);
  TheoryVar v = e->getThVar(getId());
  if (v == s_nullTheoryVar)
  {
    v = mkVar(e);
    addRowEntry<false>(rId, Rational(1), v);
    initRow(rId);
  }
  else
  {
    // Z3's HACK: n was already internalized by the calls above, which can
    // happen when one of them (indirectly) invokes mkAxiom.
    delRow(rId);
  }
  return v;
}

TheoryVar TheoryArith::internalizeMulCore(TNode t)
{
  if (!arith::isMul(t))
  {
    return internalizeTermCore(t);
  }
  for (TNode arg : t)
  {
    TheoryVar v = internalizeTermCore(arg);
    if (v == s_nullTheoryVar)
    {
      mkVar(mkENode(arg));
    }
  }
  ENode* e = mkENode(t);
  TheoryVar v = e->getThVar(getId());
  if (v == s_nullTheoryVar)
  {
    v = mkVar(e);
  }
  return v;
}

TheoryVar TheoryArith::internalizeMul(TNode m)
{
  Rational val0;
  Assert(arith::isMul(m));
  TNode arg0 = m[0];
  TNode arg1 = m[1];
  if (arith::isNumeral(arg1))
  {
    std::swap(arg0, arg1);
  }
  if (arith::isNumeral(arg0, val0) && !arith::isNumeral(arg1)
      && m.getNumChildren() == 2)
  {
    Numeral val(val0);
    if (val0.isZero())
    {
      return internalizeNumeral(m, val);
    }
    size_t rId = mkRow();
    ScopedRowVars sc(d_rowVars, d_rowVarsTop);
    checkApp(arg1, m);
    if (reflectionEnabled())
    {
      internalizeTermCore(arg0);
    }
    TheoryVar v = internalizeMulCore(arg1);
    addRowEntry<true>(rId, val, v);
    ENode* e = mkENode(m);
    TheoryVar s = mkVar(e);
    addRowEntry<false>(rId, Rational(1), s);
    initRow(rId);
    return s;
  }
  return internalizeMulCore(m);
}

TheoryVar TheoryArith::mkBinaryOp(TNode n)
{
  Assert(n.getNumChildren() == 2);
  if (d_ctx.eInternalized(n))
  {
    return expr2var(n);
  }
  d_ctx.internalize(n[0], false);
  d_ctx.internalize(n[1], false);
  ENode* e = mkENode(n);
  return mkVar(e);
}

TheoryVar TheoryArith::internalizeDiv(TNode n)
{
  Rational r(1);
  TheoryVar s = mkBinaryOp(n);
  if (!arith::isNumeral(n[1], r) || r.isZero())
  {
    foundUnderspecifiedOp(n);
  }
  if (!d_ctx.relevancy())
  {
    mkDivAxiom(n[0], n[1], arith::isTotalDivOp(n));
  }
  return s;
}

TheoryVar TheoryArith::internalizeIdiv(TNode n)
{
  Rational r;
  TheoryVar s = mkBinaryOp(n);
  if (!arith::isNumeral(n[1], r) || r.isZero())
  {
    foundUnderspecifiedOp(n);
  }
  NodeManager* nm = d_ctx.getEnv().getNodeManager();
  Node mod = nm->mkNode(arith::isTotalDivOp(n) ? Kind::INTS_MODULUS_TOTAL
                                                : Kind::INTS_MODULUS,
                        n[0],
                        n[1]);
  d_ctx.internalize(mod, false);
  if (d_ctx.relevancy())
  {
    d_ctx.addRelevancyDependency(n, mod);
  }
  return s;
}

TheoryVar TheoryArith::internalizeMod(TNode n)
{
  Rational r(1);
  TheoryVar s = mkBinaryOp(n);
  if (!arith::isNumeral(n[1], r) || r.isZero())
  {
    foundUnderspecifiedOp(n);
  }
  if (!d_ctx.relevancy())
  {
    mkIdivModAxioms(n[0], n[1], arith::isTotalDivOp(n));
  }
  return s;
}

TheoryVar TheoryArith::internalizeRem(TNode /*n*/)
{
  // cvc5 has no rem operator.
  Unreachable() << "z3: rem is not an operator of cvc5";
  return s_nullTheoryVar;
}

void TheoryArith::mkAxiom(TNode ante, TNode conseq, bool simplifyConseq)
{
  // pinned versions
  Node pAnte = ante;
  Node pConseq = conseq;
  bool negated;

  Node sAnte = d_ctx.rewriteInstance(ante);

  if (d_ctx.getCancelFlag())
  {
    return;
  }
  negated = sAnte.getKind() == Kind::NOT;
  if (negated)
  {
    sAnte = sAnte[0];
  }
  d_ctx.internalize(sAnte, false);
  Literal lAnte = d_ctx.getLiteral(sAnte);
  if (negated)
  {
    lAnte.neg();
  }

  Node sConseq = conseq;
  if (simplifyConseq)
  {
    sConseq = d_ctx.rewriteInstance(conseq);
  }
  if (d_ctx.getCancelFlag())
  {
    return;
  }
  negated = sConseq.getKind() == Kind::NOT;
  if (negated)
  {
    sConseq = sConseq[0];
  }
  d_ctx.internalize(sConseq, false);
  Literal lConseq = d_ctx.getLiteral(sConseq);
  if (negated)
  {
    lConseq.neg();
  }

  Trace("z3-arith") << "mkAxiom " << ante << " " << conseq << std::endl;
  mkClause(lAnte, lConseq);

  if (d_ctx.relevancy())
  {
    if (lAnte == s_falseLiteral)
    {
      d_ctx.markAsRelevant(lConseq);
    }
    else
    {
      // We must mark the antecedent as relevant, otherwise the core will not
      // propagate it to the theory of arithmetic.
      d_ctx.markAsRelevant(lAnte);
      // mark consequent as relevant if antecedent is false.
      d_ctx.addRelWatch(~lAnte, sConseq);
    }
  }
}

void TheoryArith::mkDivAxiom(TNode p, TNode q)
{
  mkDivAxiom(p, q, true);
}

void TheoryArith::mkDivAxiom(TNode p, TNode q, bool total)
{
  if (!isZero(q))
  {
    NodeManager* nm = d_ctx.getEnv().getNodeManager();
    Node div =
        nm->mkNode(total ? Kind::DIVISION_TOTAL : Kind::DIVISION, p, q);
    // Z3 uses a real zero; q may be an integer in cvc5.
    Node zero = NodeManager::mkConstRealOrInt(q.getType(), Rational(0));
    Node eqz = nm->mkNode(Kind::EQUAL, q, zero);
    Node eq = nm->mkNode(Kind::EQUAL, arith::mkMul(nm, q, div), p);
    mkAxiom(eqz, eq);
  }
  if (total)
  {
    NodeManager* nm = d_ctx.getEnv().getNodeManager();
    mkTotalDivZeroAxiom(nm->mkNode(Kind::DIVISION_TOTAL, p, q));
  }
}

void TheoryArith::mkIdivModAxioms(TNode dividend, TNode divisor)
{
  mkIdivModAxioms(dividend, divisor, true);
}

void TheoryArith::mkIdivModAxioms(TNode dividend, TNode divisor, bool total)
{
  NodeManager* nm = d_ctx.getEnv().getNodeManager();
  Node div = nm->mkNode(
      total ? Kind::INTS_DIVISION_TOTAL : Kind::INTS_DIVISION, dividend, divisor);
  Node mod = nm->mkNode(
      total ? Kind::INTS_MODULUS_TOTAL : Kind::INTS_MODULUS, dividend, divisor);
  if (!isZero(divisor))
  {
    // if divisor is zero, then idiv and mod are uninterpreted functions.
    Node zero = nm->mkConstInt(Rational(0));
    Node one = nm->mkConstInt(Rational(1));
    Node absDivisor = nm->mkNode(
        Kind::SUB,
        nm->mkNode(Kind::ITE,
                   nm->mkNode(Kind::LT, divisor, zero),
                   nm->mkNode(Kind::SUB, zero, divisor),
                   divisor),
        one);
    absDivisor = d_ctx.rewriteInstance(absDivisor);
    Node eqz = nm->mkNode(Kind::EQUAL, divisor, zero);
    Node qr = arith::mkAdd(nm, arith::mkMul(nm, divisor, div), mod);
    Node eq = nm->mkNode(Kind::EQUAL, qr, dividend);
    Node lower = arith::mkGe(nm, mod, zero);
    Node upper = arith::mkLe(nm, mod, absDivisor);

    mkAxiom(eqz, eq, false);
    mkAxiom(eqz, lower, false);
    mkAxiom(eqz, upper, !arith::isNumeral(absDivisor));

    Rational k;

    d_arithEqAdapter.mkAxioms(ensureENode(qr), ensureENode(dividend));

    // Z3: non-linear divisors/mod have to be flattened for the non-linear
    // solver to understand the terms; the rewriter is used to ensure this.
    Node qr1 = d_ctx.rewriteInstance(qr);
    if (qr != qr1)
    {
      Node eq2 = nm->mkNode(Kind::EQUAL, qr, qr1);
      d_ctx.internalize(eq2, false);
      Literal qeq = d_ctx.getLiteral(eq2);
      d_ctx.markAsRelevant(qeq);
      d_ctx.mkThAxiom(getId(), 1, &qeq);
      d_arithEqAdapter.mkAxioms(ensureENode(qr), ensureENode(qr1));
    }

    if (isZero(dividend))
    {
      mkAxiom(eqz, nm->mkNode(Kind::EQUAL, div, zero));
      mkAxiom(eqz, nm->mkNode(Kind::EQUAL, mod, zero));
    }
    // (or (= y 0)  (<= (* y (div x y)) x))
    else if (!arith::isNumeral(divisor))
    {
      Node divGe = arith::mkGe(
          nm, arith::mkSub(nm, dividend, arith::mkMul(nm, divisor, div)), zero);
      divGe = d_ctx.rewriteInstance(divGe);
      mkAxiom(eqz, divGe, false);
    }

    if (d_params.d_arithEnumConstMod && arith::isNumeral(divisor, k)
        && isPos(k) && k < Rational(8))
    {
      Rational j(0);
      LiteralVector lits;
      while (j < k)
      {
        Node modJ = nm->mkNode(Kind::EQUAL, mod, nm->mkConstInt(j));
        d_ctx.internalize(modJ, false);
        Literal lit(d_ctx.getLiteral(modJ));
        lits.push_back(lit);
        d_ctx.markAsRelevant(lit);
        j += Rational(1);
      }
      d_ctx.mkThAxiom(getId(), lits);
    }
  }
  if (total)
  {
    // Not from Z3: the value of the total operators at a zero divisor.
    mkTotalDivZeroAxiom(div);
    mkTotalDivZeroAxiom(mod);
  }
}

void TheoryArith::mkRemAxiom(TNode /*dividend*/, TNode /*divisor*/)
{
  // cvc5 has no rem operator.
  Unreachable() << "z3: rem is not an operator of cvc5";
}

void TheoryArith::mkTotalDivZeroAxiom(TNode n)
{
  Assert(arith::isTotalDivOp(n));
  TNode divisor = n[1];
  Rational k;
  if (arith::isNumeral(divisor, k) && !k.isZero())
  {
    // the axiom is trivially satisfied
    return;
  }
  NodeManager* nm = d_ctx.getEnv().getNodeManager();
  Node zero = NodeManager::mkConstRealOrInt(divisor.getType(), Rational(0));
  Node eqz = nm->mkNode(Kind::EQUAL, divisor, zero);
  // x div_total 0 = 0, x mod_total 0 = x, x /_total 0 = 0
  Node val = n.getKind() == Kind::INTS_MODULUS_TOTAL
                 ? Node(n[0])
                 : NodeManager::mkConstRealOrInt(n.getType(), Rational(0));
  Node eq = nm->mkNode(Kind::EQUAL, n, val);
  // (or (not (= divisor 0)) (= n val))
  mkAxiom(eqz.notNode(), eq);
}

void TheoryArith::mkToIntAxiom(TNode n)
{
  Assert(arith::isToInt(n));
  NodeManager* nm = d_ctx.getEnv().getNodeManager();
  TNode x = n[0];

  // to_int (to_real x) = x
  if (arith::isToReal(x))
  {
    mkAxiom(nm->mkConst(false), nm->mkNode(Kind::EQUAL, x[0], n));
    return;
  }
  Node toR = nm->mkNode(Kind::TO_REAL, n);
  Node diff = arith::mkAdd(
      nm, x, arith::mkMul(nm, nm->mkConstReal(Rational(-1)), toR));

  Node lo = arith::mkGe(nm, diff, nm->mkConstReal(Rational(0)));
  Node hi = arith::mkGe(nm, diff, nm->mkConstReal(Rational(1)));
  hi = hi.notNode();

  mkAxiom(nm->mkConst(false), lo, false);
  mkAxiom(nm->mkConst(false), hi, false);
}

TheoryVar TheoryArith::internalizeToInt(TNode n)
{
  Assert(n.getNumChildren() == 1);
  if (d_ctx.eInternalized(n))
  {
    return expr2var(n);
  }
  /* TheoryVar arg = */ internalizeTermCore(n[0]);
  ENode* e = mkENode(n);
  TheoryVar r = mkVar(e);
  if (!d_ctx.relevancy())
  {
    mkToIntAxiom(n);
  }
  return r;
}

void TheoryArith::mkIsIntAxiom(TNode n)
{
  // Create the axiom (iff (is_int x) (= x (to_real (to_int x))))
  Assert(arith::isIsInt(n));
  NodeManager* nm = d_ctx.getEnv().getNodeManager();
  TNode x = n[0];
  Node eq = nm->mkNode(
      Kind::EQUAL,
      nm->mkNode(Kind::TO_REAL, nm->mkNode(Kind::TO_INTEGER, x)),
      x);
  mkAxiom(n.notNode(), eq);
  mkAxiom(eq.notNode(), n);
}

void TheoryArith::internalizeIsInt(TNode n)
{
  Assert(n.getNumChildren() == 1);
  if (d_ctx.bInternalized(n))
  {
    return;
  }
  /* TheoryVar arg = */ internalizeTermCore(n[0]);
  ENode* e = mkENode(n);
  /* TheoryVar r = */ mkVar(e);
  if (!d_ctx.relevancy())
  {
    mkIsIntAxiom(n);
  }
}

TheoryVar TheoryArith::internalizeToReal(TNode n)
{
  // create the row: r - arg = 0
  Assert(n.getNumChildren() == 1);
  if (d_ctx.eInternalized(n))
  {
    return expr2var(n);
  }
  TheoryVar arg = internalizeTermCore(n[0]);
  // n may be internalized by the call above if n is of the form
  // (to_real (to_int t)).
  if (d_ctx.eInternalized(n))
  {
    return expr2var(n);
  }
  ENode* e = mkENode(n);
  TheoryVar r = mkVar(e);
  size_t rId = mkRow();
  ScopedRowVars sc(d_rowVars, d_rowVarsTop);
  addRowEntry<true>(rId, Rational(1), arg);
  addRowEntry<false>(rId, Rational(1), r);
  initRow(rId);
  return r;
}

TheoryVar TheoryArith::internalizeNumeral(TNode n)
{
  Rational val;
  bool isNum = arith::isNumeral(n, val);
  AlwaysAssert(isNum);
  return internalizeNumeral(n, val);
}

TheoryVar TheoryArith::internalizeNumeral(TNode n, const Numeral& val)
{
  if (d_ctx.eInternalized(n))
  {
    return mkVar(d_ctx.getENode(n));
  }
  ENode* e = mkENode(n);
  TheoryVar v = mkVar(e);
  InfNumeral ival(val);
  Bound* l = new Bound(v, ival, B_LOWER, false);
  Bound* u = new Bound(v, ival, B_UPPER, false);
  setBound(l, false);
  setBound(u, true);
  d_boundsToDelete.push_back(l);
  d_boundsToDelete.push_back(u);
  d_value[v] = ival;
  return v;
}


TheoryVar TheoryArith::internalizeTermCore(TNode n)
{
  if (d_ctx.eInternalized(n))
  {
    ENode* e = d_ctx.getENode(n);
    if (isAttachedToVar(e))
    {
      return e->getThVar(getId());
    }
  }

  Assert(!arith::isUminus(n));

  if (arith::isAdd(n))
  {
    return internalizeAdd(n);
  }
  else if (arith::isMul(n))
  {
    return internalizeMul(n);
  }
  else if (arith::isDiv(n))
  {
    return internalizeDiv(n);
  }
  else if (arith::isIdiv(n))
  {
    return internalizeIdiv(n);
  }
  else if (arith::isMod(n))
  {
    return internalizeMod(n);
  }
  else if (arith::isToReal(n))
  {
    return internalizeToReal(n);
  }
  else if (arith::isToInt(n))
  {
    return internalizeToInt(n);
  }
  else if (arith::isNumeral(n))
  {
    return internalizeNumeral(n);
  }
  else if (arith::isSub(n))
  {
    return internalizeSub(n);
  }
  if (n.getKind() == Kind::POW)
  {
    // unsupported
    foundUnsupportedOp(n);
    return mkBinaryOp(n);
  }
  if (n.getKind() == Kind::REAL_ALGEBRAIC_NUMBER)
  {
    // unsupported
    foundUnsupportedOp(n);
    ENode* e = mkENode(n);
    return mkVar(e);
  }
  if (isArithFamily(n))
  {
    // cvc5 has no div0/mod0/idiv0/rem0
    foundUnsupportedOp(n);
    if (d_ctx.eInternalized(n))
    {
      return expr2var(n);
    }
    for (TNode arg : n)
    {
      d_ctx.internalize(arg, false);
    }
    return mkVar(mkENode(n));
  }

  if (!d_ctx.eInternalized(n))
  {
    if (isArithLeaf(n))
    {
      // Not from Z3: see isArithLeaf; this is what the core's
      // internalizeUninterpreted does for a constant.
      d_ctx.mkENode(n, false, false, true);
    }
    else
    {
      d_ctx.internalize(n, false);
    }
  }
  ENode* e = d_ctx.getENode(n);
  if (!isAttachedToVar(e))
  {
    return mkVar(e);
  }
  return e->getThVar(getId());
}

size_t TheoryArith::mkRow()
{
  size_t r;
  if (d_deadRows.empty())
  {
    r = d_rows.size();
    d_rows.push_back(Row());
  }
  else
  {
    r = d_deadRows.back();
    d_deadRows.pop_back();
  }
  d_inToCheck.assureDomain(r);
  Assert(d_rows[r].size() == 0);
  Assert(d_rows[r].numEntries() == 0);
  d_stats.d_tableauMaxRows = std::max(d_stats.d_tableauMaxRows,
                                      static_cast<uint64_t>(d_rows.size()));
  return r;
}

void TheoryArith::initRow(size_t rId)
{
  Row& r = d_rows[rId];
  Assert(r.d_firstFreeIdx == -1);
  Assert(r.size() != 0);
  Assert(r.size() == r.numEntries());
  Assert(r[r.size() - 1].d_coeff.isOne());
  TheoryVar s = r[r.size() - 1].d_var;
  r.d_baseVar = s;
  setVarRow(s, rId);
  if (lazyPivotingLvl() > 2)
  {
    setVarKind(s, QUASI_BASE);
    normalizeQuasiBaseRow(rId);
  }
  else
  {
    normalizeBaseRow(rId);
    Assert(getVarKind(s) == BASE);
  }
  if (propagationMode() != BP_NONE)
  {
    markRowForBoundProp(rId);
  }
}

void TheoryArith::collectVars(size_t rId,
                              VarKind k,
                              std::vector<LinearMonomial>& result)
{
  Row& r = d_rows[rId];
  TheoryVar base = r.d_baseVar;
  for (const RowEntry& re : r.d_entries)
  {
    if (!re.isDead() && getVarKind(re.d_var) == k && re.d_var != base)
    {
      Numeral c = -re.d_coeff;
      result.push_back(LinearMonomial(c, re.d_var));
    }
  }
}

void TheoryArith::normalizeQuasiBaseRow(size_t rId)
{
  std::vector<LinearMonomial> toAdd;
  collectVars(rId, QUASI_BASE, toAdd);
  addRows(rId, toAdd.size(), toAdd.data());
}

void TheoryArith::quasiBaseRow2BaseRow(size_t rId)
{
  std::vector<LinearMonomial> toAdd;
  collectVars(rId, BASE, toAdd);
  addRows(rId, toAdd.size(), toAdd.data());
  TheoryVar s = d_rows[rId].getBaseVar();
  setVarKind(s, BASE);
  InfNumeral tmp;
  if (getImpliedOldValue(s, tmp))
  {
    // Necessary because of restoreAssignment: the value of s must be
    // compatible with the old values of the variables it depends on.
    d_value[s] = tmp;
    Assert(!d_inUpdateTrailStack.contains(s));
    saveValue(s);
  }
  d_value[s] = getImpliedValue(s);
}

void TheoryArith::normalizeBaseRow(size_t rId)
{
  if (lazyPivotingLvl() > 0)
  {
    normalizeQuasiBaseRow(rId);
  }
  quasiBaseRow2BaseRow(rId);
}

void TheoryArith::mkClause(Literal l1, Literal l2)
{
  d_ctx.mkThAxiom(getId(), l1, l2);
}

void TheoryArith::mkClause(Literal l1, Literal l2, Literal l3)
{
  d_ctx.mkThAxiom(getId(), l1, l2, l3);
}

void TheoryArith::mkBoundAxioms(Atom* a1)
{
  TheoryVar v = a1->getVar();
  Atoms& occs = d_varOccs[v];
  if (!d_ctx.isSearching())
  {
    // NB. Z3 assumes that user push calls propagation before internal
    // scopes are pushed. This flushes all newly asserted atoms into the
    // right context.
    d_newAtoms.push_back(a1);
    return;
  }
  const InfNumeral& k1(a1->getK());
  AtomKind kind1 = a1->getAtomKind();

  Atoms::iterator it = occs.begin();
  Atoms::iterator end = occs.end();
  Atoms::iterator loInf = end, loSup = end;
  Atoms::iterator hiInf = end, hiSup = end;

  for (; it != end; ++it)
  {
    Atom* a2 = *it;
    const InfNumeral& k2(a2->getK());
    AtomKind kind2 = a2->getAtomKind();

    if (k1 == k2 && kind1 == kind2)
    {
      continue;
    }

    if (kind2 == A_LOWER)
    {
      if (k2 < k1)
      {
        if (loInf == end || k2 > (*loInf)->getK())
        {
          loInf = it;
        }
      }
      else if (loSup == end || k2 < (*loSup)->getK())
      {
        loSup = it;
      }
    }
    else if (k2 < k1)
    {
      if (hiInf == end || k2 > (*hiInf)->getK())
      {
        hiInf = it;
      }
    }
    else if (hiSup == end || k2 < (*hiSup)->getK())
    {
      hiSup = it;
    }
  }
  if (loInf != end) mkBoundAxiom(a1, *loInf);
  if (loSup != end) mkBoundAxiom(a1, *loSup);
  if (hiInf != end) mkBoundAxiom(a1, *hiInf);
  if (hiSup != end) mkBoundAxiom(a1, *hiSup);
}

void TheoryArith::mkBoundAxiom(Atom* a1, Atom* a2)
{
  TheoryVar v = a1->getVar();
  Literal l1(a1->getBoolVar());
  Literal l2(a2->getBoolVar());
  const InfNumeral& k1(a1->getK());
  const InfNumeral& k2(a2->getK());
  AtomKind kind1 = a1->getAtomKind();
  AtomKind kind2 = a2->getAtomKind();
  bool vIsInt = isInt(v);
  Assert(v == a2->getVar());
  if (k1 == k2 && kind1 == kind2) return;

  if (kind1 == A_LOWER)
  {
    if (kind2 == A_LOWER)
    {
      if (k2 <= k1)
      {
        mkClause(~l1, l2);
      }
      else
      {
        mkClause(l1, ~l2);
      }
    }
    else if (k1 <= k2)
    {
      // k1 <= k2, k1 <= x or x <= k2
      mkClause(l1, l2);
    }
    else
    {
      // k1 > hi_inf, k1 <= x => ~(x <= hi_inf)
      mkClause(~l1, ~l2);
      if (vIsInt && k1 == k2 + InfNumeral(1))
      {
        // k1 <= x or x <= k1-1
        mkClause(l1, l2);
      }
    }
  }
  else if (kind2 == A_LOWER)
  {
    if (k1 >= k2)
    {
      // k1 >= lo_inf, k1 >= x or lo_inf <= x
      mkClause(l1, l2);
    }
    else
    {
      // k1 < k2, k2 <= x => ~(x <= k1)
      mkClause(~l1, ~l2);
      if (vIsInt && k1 == k2 - InfNumeral(1))
      {
        // x <= k1 or k1+l <= x
        mkClause(l1, l2);
      }
    }
  }
  else
  {
    // kind1 == A_UPPER, kind2 == A_UPPER
    if (k1 >= k2)
    {
      // k1 >= k2, x <= k2 => x <= k1
      mkClause(l1, ~l2);
    }
    else
    {
      // k1 <= hi_sup , x <= k1 =>  x <= hi_sup
      mkClause(~l1, l2);
    }
  }
}

void TheoryArith::flushBoundAxioms()
{
  while (!d_newAtoms.empty())
  {
    std::vector<Atom*> atoms;
    atoms.push_back(d_newAtoms.back());
    d_newAtoms.pop_back();
    TheoryVar v = atoms.back()->getVar();
    for (size_t i = 0; i < d_newAtoms.size(); ++i)
    {
      if (d_newAtoms[i]->getVar() == v)
      {
        atoms.push_back(d_newAtoms[i]);
        d_newAtoms[i] = d_newAtoms.back();
        d_newAtoms.pop_back();
        --i;
      }
    }
    Atoms occs(d_varOccs[v]);

    std::sort(atoms.begin(), atoms.end(), CompareAtoms());
    std::sort(occs.begin(), occs.end(), CompareAtoms());

    Atoms::iterator begin1 = occs.begin();
    Atoms::iterator begin2 = occs.begin();
    Atoms::iterator end = occs.end();
    begin1 = first(A_LOWER, begin1, end);
    begin2 = first(A_UPPER, begin2, end);

    Atoms::iterator loInf = begin1, loSup = begin1;
    Atoms::iterator hiInf = begin2, hiSup = begin2;
    Atoms::iterator loInf1 = begin1, loSup1 = begin1;
    Atoms::iterator hiInf1 = begin2, hiSup1 = begin2;
    bool floInf, fhiInf, floSup, fhiSup;
    std::unordered_set<Atom*> visited;
    for (size_t i = 0; i < atoms.size(); ++i)
    {
      Atom* a1 = atoms[i];
      loInf1 = nextInf(a1, A_LOWER, loInf, end, floInf);
      hiInf1 = nextInf(a1, A_UPPER, hiInf, end, fhiInf);
      loSup1 = nextSup(a1, A_LOWER, loSup, end, floSup);
      hiSup1 = nextSup(a1, A_UPPER, hiSup, end, fhiSup);
      if (loInf1 != end) loInf = loInf1;
      if (loSup1 != end) loSup = loSup1;
      if (hiInf1 != end) hiInf = hiInf1;
      if (hiSup1 != end) hiSup = hiSup1;
      if (!floInf) loInf = end;
      if (!fhiInf) hiInf = end;
      if (!floSup) loSup = end;
      if (!fhiSup) hiSup = end;
      visited.insert(a1);
      if (loInf1 != end && loInf != end && visited.count(*loInf) == 0)
        mkBoundAxiom(a1, *loInf);
      if (loSup1 != end && loSup != end && visited.count(*loSup) == 0)
        mkBoundAxiom(a1, *loSup);
      if (hiInf1 != end && hiInf != end && visited.count(*hiInf) == 0)
        mkBoundAxiom(a1, *hiInf);
      if (hiSup1 != end && hiSup != end && visited.count(*hiSup) == 0)
        mkBoundAxiom(a1, *hiSup);
    }
  }
}

TheoryArith::Atoms::iterator TheoryArith::first(AtomKind kind,
                                                Atoms::iterator it,
                                                Atoms::iterator end)
{
  for (; it != end; ++it)
  {
    Atom* a = *it;
    if (a->getAtomKind() == kind) return it;
  }
  return end;
}

TheoryArith::Atoms::iterator TheoryArith::nextInf(Atom* a1,
                                                  AtomKind kind,
                                                  Atoms::iterator it,
                                                  Atoms::iterator end,
                                                  bool& foundCompatible)
{
  const InfNumeral& k1(a1->getK());
  Atoms::iterator result = end;
  foundCompatible = false;
  for (; it != end; ++it)
  {
    Atom* a2 = *it;
    if (a1 == a2) continue;
    if (a2->getAtomKind() != kind) continue;
    const InfNumeral& k2(a2->getK());
    foundCompatible = true;
    if (k2 <= k1)
    {
      result = it;
    }
    else
    {
      break;
    }
  }
  return result;
}

TheoryArith::Atoms::iterator TheoryArith::nextSup(Atom* a1,
                                                  AtomKind kind,
                                                  Atoms::iterator it,
                                                  Atoms::iterator end,
                                                  bool& foundCompatible)
{
  const InfNumeral& k1(a1->getK());
  foundCompatible = false;
  for (; it != end; ++it)
  {
    Atom* a2 = *it;
    if (a1 == a2) continue;
    if (a2->getAtomKind() != kind) continue;
    const InfNumeral& k2(a2->getK());
    foundCompatible = true;
    if (k1 < k2)
    {
      return it;
    }
  }
  return end;
}

bool TheoryArith::internalizeAtom(TNode n, bool /*gateCtx*/)
{
  Assert(!d_ctx.bInternalized(n));
  AtomKind kind;

  if (arith::isIsInt(n))
  {
    internalizeIsInt(n);
    if (d_ctx.bInternalized(n))
    {
      return true;
    }
    BoolVar bv = d_ctx.mkBoolVar(n);
    d_ctx.setVarTheory(bv, getId());
    return true;
  }
  if (!arith::isLe(n) && !arith::isGe(n))
  {
    // Not from Z3: strict inequalities (which cvc5's rewriter eliminates) and
    // the other arithmetic predicates of cvc5 are not supported.
    foundUnsupportedOp(n);
    return false;
  }
  if (arith::isLe(n))
  {
    kind = A_UPPER;
  }
  else
  {
    kind = A_LOWER;
  }
  if (!isApp(n[0]) || !isApp(n[1]))
  {
    return false;
  }
  TNode lhs = n[0];
  TNode rhs = n[1];
  if (arith::isToReal(rhs) && isApp(rhs[0]))
  {
    rhs = rhs[0];
  }
  if (!arith::isNumeral(rhs))
  {
    throw Exception("malformed atomic constraint");
  }
  TheoryVar v = internalizeTermCore(lhs);
  if (v == s_nullTheoryVar)
  {
    return false;
  }
  if (d_ctx.bInternalized(n))
  {
    return true;
  }
  BoolVar bv = d_ctx.mkBoolVar(n);
  d_ctx.setVarTheory(bv, getId());
  Rational k0;
  bool isNum = arith::isNumeral(rhs, k0);
  AlwaysAssert(isNum);
  if (isInt(v) && !k0.isIntegral())
  {
    if (kind == A_UPPER)
    {
      k0 = floor(k0);
    }
    else
    {
      k0 = ceil(k0);
    }
  }
  InfNumeral k(k0);
  Atom* a = new Atom(bv, v, k, kind);
  mkBoundAxioms(a);
  d_unassignedAtoms[v]++;
  Atoms& occs = d_varOccs[v];
  occs.push_back(a);
  d_atoms.push_back(a);
  insertBv2a(bv, a);
  return true;
}

bool TheoryArith::internalizeTerm(TNode term)
{
  if (isArithLeaf(term))
  {
    // Not from Z3: see isArithLeaf. Z3 gives the constant an enode as an
    // uninterpreted term, and a theory variable only when it occurs in an
    // arithmetic context (internalizeTermCore).
    if (!d_ctx.eInternalized(term))
    {
      d_ctx.mkENode(term, false, false, true);
    }
    return true;
  }
  TheoryVar v = internalizeTermCore(term);
  return v != s_nullTheoryVar;
}

void TheoryArith::internalizeEqEh(TNode atom, BoolVar /*v*/)
{
  if (d_params.d_arithEagerEqAxioms && atom.getKind() == Kind::EQUAL
      && isApp(atom[0]) && isApp(atom[1]))
  {
    TNode lhs = atom[0];
    TNode rhs = atom[1];
    ENode* n1 = d_ctx.getENode(lhs);
    ENode* n2 = d_ctx.getENode(rhs);
    // The atom may be a theory axiom, not in simplified form, e.g. (= a a).
    if (n1->getThVar(getId()) != s_nullTheoryVar
        && n2->getThVar(getId()) != s_nullTheoryVar && n1 != n2)
    {
      d_arithEqAdapter.mkAxioms(n1, n2);
    }
  }
}

void TheoryArith::applySortCnstr(ENode* /*n*/, const TypeNode& /*s*/)
{
  // do nothing...
}

void TheoryArith::assignEh(BoolVar v, bool isTrue)
{
  Atom* a = getBv2a(v);
  if (!a) return;
  Assert(d_ctx.getAssignment(a->getBoolVar()) != L_UNDEF);
  Assert((d_ctx.getAssignment(a->getBoolVar()) == L_TRUE) == isTrue);
  a->assignEh(isTrue, getEpsilon(a->getVar()));
  d_assertedBounds.push_back(a);
}

void TheoryArith::relevantEh(TNode n)
{
  if (arith::isMod(n))
  {
    mkIdivModAxioms(n[0], n[1], arith::isTotalDivOp(n));
  }
  else if (arith::isDiv(n))
  {
    mkDivAxiom(n[0], n[1], arith::isTotalDivOp(n));
  }
  else if (arith::isToInt(n))
  {
    mkToIntAxiom(n);
  }
  else if (arith::isIsInt(n))
  {
    mkIsIntAxiom(n);
  }
}

void TheoryArith::newEqEh(TheoryVar v1, TheoryVar v2)
{
  ENode* n1 = getENode(v1);

  if (!n1->getExpr().getType().isRealOrInt())
  {
    return;
  }
  if (d_params.d_arithEqBounds)
  {
    ENode* n2 = getENode(v2);
    Assert(n1->getRoot() == n2->getRoot());
    if (arith::isNumeral(n1->getExpr()))
    {
      std::swap(v1, v2);
      std::swap(n1, n2);
    }
    Rational k;
    Bound* b1 = nullptr;
    Bound* b2 = nullptr;
    if (arith::isNumeral(n2->getExpr(), k))
    {
      InfNumeral val(k);
      b1 = new EqBound(v1, val, B_LOWER, n1, n2);
      b2 = new EqBound(v1, val, B_UPPER, n1, n2);
    }
    else
    {
      if (n1->getOwnerId() > n2->getOwnerId())
      {
        std::swap(n1, n2);
      }
      NodeManager* nm = d_ctx.getEnv().getNodeManager();
      TypeNode st = n1->getExpr().getType();
      Node minusOne = NodeManager::mkConstRealOrInt(st, Rational(-1));
      Node s = nm->mkNode(Kind::ADD,
                          n1->getExpr(),
                          nm->mkNode(Kind::MULT, minusOne, n2->getExpr()));
      d_ctx.internalize(s, false);
      ENode* eS = d_ctx.getENode(s);
      d_ctx.markAsRelevant(eS);
      Assert(isAttachedToVar(eS));
      TheoryVar vS = eS->getThVar(getId());
      b1 = new EqBound(vS, InfNumeral(), B_LOWER, n1, n2);
      b2 = new EqBound(vS, InfNumeral(), B_UPPER, n1, n2);
    }
    d_boundsToDelete.push_back(b1);
    d_boundsToDelete.push_back(b2);
    d_assertedBounds.push_back(b1);
    d_assertedBounds.push_back(b2);
  }
  else
  {
    d_arithEqAdapter.newEqEh(v1, v2);
  }
}

bool TheoryArith::useDiseqs() const { return true; }

void TheoryArith::newDiseqEh(TheoryVar v1, TheoryVar v2)
{
  d_stats.d_assertDiseq++;
  d_arithEqAdapter.newDiseqEh(v1, v2);
}

void TheoryArith::restartEh() { d_arithEqAdapter.restartEh(); }

void TheoryArith::initSearchEh()
{
  d_numConflicts = 0;
  d_branchCutCounter = 0;
  d_eagerGcd = d_params.d_arithEagerGcd;
  if (lazyPivotingLvl() == 1)
  {
    elimQuasiBaseRows();
  }
  moveUnconstrainedToBase();
  d_arithEqAdapter.initSearchEh();
  d_finalCheckIdx = 0;
  // m_nl_gb_exhausted and m_nl_strategy_idx belong to the Groebner
  // machinery, which is not ported.
}

FinalCheckStatus TheoryArith::finalCheckCore()
{
  d_modelDependsOnComputedEpsilon = false;
  size_t oldIdx = d_finalCheckIdx;
  FinalCheckStatus result = FC_DONE;
  FinalCheckStatus ok;
  do
  {
    if (d_ctx.getCancelFlag())
    {
      return FC_GIVEUP;
    }

    Assert(d_toPatch.empty());

    switch (d_finalCheckIdx)
    {
      case 0: ok = checkIntFeasibility(); break;
      case 1:
        if (assumeEqs())
        {
          ok = FC_CONTINUE;
        }
        else
        {
          ok = FC_DONE;
        }
        break;
      default: ok = processNonLinear(); break;
    }
    Trace("z3-arith") << "final check idx " << d_finalCheckIdx << ": " << ok
                      << std::endl;
    d_finalCheckIdx = (d_finalCheckIdx + 1) % 3;
    switch (ok)
    {
      case FC_DONE: break;
      case FC_GIVEUP: result = FC_GIVEUP; break;
      case FC_CONTINUE: return FC_CONTINUE;
    }
  } while (d_finalCheckIdx != oldIdx);
  if (result == FC_DONE)
  {
    for (const Node& n : d_unsupportedOps)
    {
      if (!d_ctx.isRelevant(n))
      {
        continue;
      }
      Trace("z3-arith") << "Found unsupported operation " << n << std::endl;
      result = FC_GIVEUP;
    }
  }
  return result;
}

FinalCheckStatus TheoryArith::finalCheckEh(size_t /*level*/)
{
  if (!propagateCore())
  {
    return FC_CONTINUE;
  }
  if (delayedAssumeEqs())
  {
    return FC_CONTINUE;
  }
  d_ctx.pushTrail(ValueTrail<size_t>(d_finalCheckIdx));
  d_liberalFinalCheck = true;
  d_changedAssignment = false;
  FinalCheckStatus result = finalCheckCore();
  if (result != FC_DONE)
  {
    return result;
  }
  if (!d_changedAssignment)
  {
    return FC_DONE;
  }
  d_liberalFinalCheck = false;
  d_changedAssignment = false;
  result = finalCheckCore();
  return result;
}

bool TheoryArith::canPropagate()
{
  return processAtoms() && d_assertedQhead < d_assertedBounds.size();
}

void TheoryArith::propagate()
{
  if (!processAtoms())
  {
    return;
  }
  propagateCore();
}

bool TheoryArith::propagateCore()
{
  flushBoundAxioms();
  propagateLinearMonomials();
  while (d_assertedQhead < d_assertedBounds.size())
  {
    Bound* b = d_assertedBounds[d_assertedQhead];
    d_assertedQhead++;
    if (!assertBound(b))
    {
      failed();
      return false;
    }
  }
  if (!makeFeasible())
  {
    failed();
    return false;
  }
  if (d_ctx.getCancelFlag())
  {
    return true;
  }

  discardUpdateTrail();

  Assert(d_updateTrailStack.empty());

  propagateBounds();
  Assert(d_assertedQhead == d_assertedBounds.size());
  Assert(d_updateTrailStack.empty());
  return true;
}

void TheoryArith::failed()
{
  restoreAssignment();
  d_toPatch.reset();
  d_toCheck.clear();
  d_inToCheck.reset();
}

void TheoryArith::flushEh()
{
  for (Atom* a : d_atoms)
  {
    delete a;
  }
  d_atoms.clear();
  for (Bound* b : d_boundsToDelete)
  {
    delete b;
  }
  d_boundsToDelete.clear();
}

void TheoryArith::resetEh()
{
  d_stats = TheoryArithStats();
  d_rows.clear();
  d_arithEqAdapter.resetEh();
  d_deadRows.clear();
  d_columns.clear();
  d_data.clear();
  d_value.clear();
  d_oldValue.clear();
  d_bounds[0].clear();
  d_bounds[1].clear();
  d_varOccs.clear();
  d_unassignedAtoms.clear();
  d_boolVar2Atom.clear();
  d_varPos.clear();
  for (Atom* a : d_atoms)
  {
    delete a;
  }
  d_atoms.clear();
  for (Bound* b : d_boundsToDelete)
  {
    delete b;
  }
  d_boundsToDelete.clear();
  d_assertedBounds.clear();
  d_assertedQhead = 0;
  d_toPatch.reset();
  d_leftBasis.reset();
  d_blandsRule = false;
  d_updateTrailStack.clear();
  d_inUpdateTrailStack.reset();
  d_toCheck.clear();
  d_inToCheck.reset();
  d_numConflicts = 0;
  d_boundTrail.clear();
  d_unassignedAtomsTrail.clear();
  d_scopes.clear();
  d_nlMonomials.clear();
  d_nlPropagated.clear();
  d_nlRounds = 0;
  Theory::resetEh();
}

const TheoryArith::InfNumeral& TheoryArith::getImpliedValue(TheoryVar v) const
{
  Assert(isQuasiBase(v) || isBase(v));
  InfNumeral& sum = const_cast<TheoryArith*>(this)->d_tmp;
  sum.reset();
  size_t rId = getVarRow(v);
  const Row& r = d_rows[rId];
  for (const RowEntry& re : r)
  {
    if (!re.isDead() && re.d_var != v)
    {
      Assert(!isQuasiBase(re.d_var));
      Assert(getValue(re.d_var) == d_value[re.d_var]);
      sum += re.d_coeff * getValue(re.d_var);
    }
  }
  sum.neg();
  return sum;
}

bool TheoryArith::getImpliedOldValue(TheoryVar v, InfNumeral& result) const
{
  Assert(isQuasiBase(v) || isBase(v));
  bool isDiff = false;
  result.reset();
  size_t rId = getVarRow(v);
  const Row& r = d_rows[rId];
  for (const RowEntry& re : r)
  {
    if (!re.isDead() && re.d_var != v)
    {
      TheoryVar v2 = re.d_var;
      Assert(!isQuasiBase(v2));
      Assert(getValue(v2) == d_value[v2]);
      if (d_inUpdateTrailStack.contains(v2))
      {
        result += re.d_coeff * d_oldValue[v2];
        isDiff = true;
      }
      else
      {
        result += re.d_coeff * d_value[v2];
      }
    }
  }
  result.neg();
  return isDiff;
}

TheoryArith::TheoryArith(SmtContext& ctx)
    : Theory(ctx, theory::THEORY_ARITH),
      d_intEpsilon(Rational(1)),
      d_realEpsilon(Rational(0), true),
      d_params(ctx.getParams()),
      d_arithEqAdapter(*this),
      d_toPatch(1024),
      d_random(ctx.getParams().d_arithRandomSeed),
      d_eagerGcd(d_params.d_arithEagerGcd),
      d_antecedentsIndex(0),
      d_varValueTable(*this),
      d_epsilon(Rational(1))
{
}

TheoryArith::~TheoryArith()
{
  // Z3 relies on flush_eh; anything left is released here.
  for (Atom* a : d_atoms)
  {
    delete a;
  }
  d_atoms.clear();
  for (Bound* b : d_boundsToDelete)
  {
    delete b;
  }
  d_boundsToDelete.clear();
}

void TheoryArith::setup()
{
  d_random.setSeed(d_params.d_arithRandomSeed);
  Theory::setup();
}

// ---------------------------------------------------------------------------
// Add Row
// ---------------------------------------------------------------------------

void TheoryArith::addRow(size_t rid1,
                         const Numeral& coeff,
                         size_t rid2,
                         bool applyGcdTest)
{
  d_stats.d_addRows++;
  if (propagationMode() != BP_NONE)
  {
    markRowForBoundProp(rid1);
  }
  Row& r1 = d_rows[rid1];
  Row& r2 = d_rows[rid2];
  r1.compressIfNeeded(d_columns);
  r2.compressIfNeeded(d_columns);

  r1.saveVarPos(d_varPos);

  // loop over variables in row2, add terms in row2 to row1.
  int mode = coeff.isOne() ? 0 : (isMinusOne(coeff) ? 1 : 2);
  for (const RowEntry& it : r2.d_entries)
  {
    if (!it.isDead())
    {
      TheoryVar v = it.d_var;
      int pos = d_varPos[v];
      if (pos == -1)
      {
        // variable v is not in row1
        int rowIdx;
        RowEntry& rEntry = r1.addRowEntry(rowIdx);
        rEntry.d_var = v;
        switch (mode)
        {
          case 0: rEntry.d_coeff = it.d_coeff; break;
          case 1: rEntry.d_coeff = -it.d_coeff; break;
          default:
            rEntry.d_coeff = it.d_coeff;
            rEntry.d_coeff *= coeff;
            break;
        }
        Column& c = d_columns[v];
        int colIdx;
        ColEntry& cEntry = c.addColEntry(colIdx);
        rEntry.d_colIdx = colIdx;
        cEntry.d_rowId = static_cast<int>(rid1);
        cEntry.d_rowIdx = rowIdx;
      }
      else
      {
        // variable v is in row1
        RowEntry& rEntry = r1[pos];
        Assert(rEntry.d_var == v);
        switch (mode)
        {
          case 0: rEntry.d_coeff += it.d_coeff; break;
          case 1: rEntry.d_coeff -= it.d_coeff; break;
          default: rEntry.d_coeff += it.d_coeff * coeff; break;
        }
        if (rEntry.d_coeff.isZero())
        {
          int colIdx = rEntry.d_colIdx;
          r1.delRowEntry(pos);
          Column& c = d_columns[v];
          c.delColEntry(colIdx);
        }
        d_varPos[v] = -1;
      }
    }
  }

  r1.resetVarPos(d_varPos);
  if (applyGcdTest)
  {
    TheoryVar v = r1.getBaseVar();
    if (isInt(v) && !getValue(v).isInt())
    {
      gcdTest(r1);
    }
  }
}

void TheoryArith::addRows(size_t r1, size_t sz, LinearMonomial* aXs)
{
  if (sz == 0)
  {
    return;
  }
  for (size_t i = 0; i < sz; ++i)
  {
    LinearMonomial& m = aXs[i];
    Numeral c = m.d_coeff;
    TheoryVar v = m.d_var;
    Assert(!isNonBase(v));
    addRow(r1, c, getVarRow(v), false);
  }
  // m.limit().inc(sz): resource limits are not ported
}

// ---------------------------------------------------------------------------
// Assignment management
// ---------------------------------------------------------------------------

void TheoryArith::saveValue(TheoryVar v)
{
  Assert(!isQuasiBase(v));
  if (!d_inUpdateTrailStack.contains(v))
  {
    d_inUpdateTrailStack.insert(v);
    Assert(d_value[v] == getValue(v));
    d_oldValue[v] = d_value[v];
    d_updateTrailStack.push_back(v);
  }
  d_changedAssignment = true;
}

void TheoryArith::discardUpdateTrail()
{
  d_inUpdateTrailStack.reset();
  d_updateTrailStack.clear();
}

void TheoryArith::restoreAssignment()
{
  for (size_t v : d_updateTrailStack)
  {
    Assert(!isQuasiBase(v));
    Assert(d_inUpdateTrailStack.contains(v));
    d_value[v] = d_oldValue[v];
  }
  d_updateTrailStack.clear();
  d_inUpdateTrailStack.reset();
}

void TheoryArith::updateValueCore(TheoryVar v, const InfNumeral& delta)
{
  saveValue(v);
  d_value[v] += delta;
  if (isBase(v) && !d_toPatch.contains(v) && (belowLower(v) || aboveUpper(v)))
  {
    d_toPatch.insert(v);
  }
  // m.limit().inc(): resource limits are not ported
}

void TheoryArith::updateValue(TheoryVar v, const InfNumeral& delta)
{
  updateValueCore(v, delta);

  Column& c = d_columns[v];
  c.compressIfNeeded(d_rows);

  InfNumeral delta2;
  for (const ColEntry& ce : c)
  {
    if (!ce.isDead())
    {
      Row& r = d_rows[ce.d_rowId];
      TheoryVar s = r.getBaseVar();
      if (s != s_nullTheoryVar && !isQuasiBase(s))
      {
        delta2 = delta;
        delta2 *= r[ce.d_rowIdx].d_coeff;
        delta2.neg();
        updateValueCore(s, delta2);
      }
    }
  }
}

// ---------------------------------------------------------------------------
// Pivoting
// ---------------------------------------------------------------------------

template <bool Lazy>
void TheoryArith::pivot(TheoryVar xI,
                        TheoryVar xJ,
                        const Numeral& aIJ,
                        bool applyGcdTest)
{
  d_stats.d_pivots++;
  Assert(isBase(xI) || isQuasiBase(xI));
  Assert(xI != xJ);

  size_t rId = getVarRow(xI);
  Row& r = d_rows[rId];

  if (isMinusOne(aIJ))
  {
    for (RowEntry& it : r.d_entries)
    {
      if (!it.isDead())
      {
        it.d_coeff = -it.d_coeff;
      }
    }
  }
  else if (!aIJ.isOne())
  {
    Numeral tmp = aIJ;
    for (RowEntry& it : r.d_entries)
    {
      if (!it.isDead())
      {
        it.d_coeff /= tmp;
      }
    }
  }

  // m.limit().inc(r.size()): resource limits are not ported

  setVarRow(xI, static_cast<size_t>(-1));
  setVarRow(xJ, rId);

  Assert(r.d_baseVar == xI);
  r.d_baseVar = xJ;

  setVarKind(xI, NON_BASE);
  setVarKind(xJ, BASE);

  eliminate<Lazy>(xJ, applyGcdTest);
}

template <bool Lazy>
void TheoryArith::eliminate(TheoryVar xI, bool applyGcdTest)
{
  Assert(isBase(xI) || isQuasiBase(xI));
  size_t rId = getVarRow(xI);
  Column& c = d_columns[xI];
  Numeral aKJ;
  int i = 0;
  int sPos = -1;
  // Z3 iterates the column entries with iterators fixed at the start.
  size_t numEntries = c.numEntries();
  for (size_t idx = 0; idx < numEntries; ++idx, ++i)
  {
    ColEntry& it = c[idx];
    if (!it.isDead())
    {
      if (it.d_rowId != static_cast<int>(rId))
      {
        Row& r2 = d_rows[it.d_rowId];
        TheoryVar s2 = r2.d_baseVar;
        if (s2 != s_nullTheoryVar && (!Lazy || isBase(s2)))
        {
          aKJ = r2[it.d_rowIdx].d_coeff;
          aKJ = -aKJ;
          addRow(it.d_rowId, aKJ, rId, applyGcdTest);
          // m.limit().inc(...): resource limits are not ported
        }
      }
      else
      {
        sPos = i;
      }
    }
  }
  Assert(Lazy || c.size() == 1);
  if (c.size() == 1)
  {
    // When lazy pivoting is used, then after pivoting c may not be a
    // singleton
    c.compressSingleton(d_rows, sPos);
  }
}

void TheoryArith::updateAndPivot(TheoryVar xI,
                                 TheoryVar xJ,
                                 const Numeral& aIJ,
                                 const InfNumeral& xINewVal)
{
  Assert(isBase(xI));
  InfNumeral theta = d_value[xI];
  theta -= xINewVal;
  theta /= aIJ;
  updateValue(xJ, theta);
  Assert(getValue(xI) == xINewVal);
  if (!d_toPatch.contains(xJ) && (belowLower(xJ) || aboveUpper(xJ)))
  {
    d_toPatch.insert(xJ);
  }
  pivot<true>(xI, xJ, aIJ, d_eagerGcd);
}

int TheoryArith::getNumNonFreeDepVars(TheoryVar v, int bestSoFar)
{
  int result = isNonFree(v);
  Column& c = d_columns[v];
  for (const ColEntry& it : c)
  {
    if (!it.isDead())
    {
      Row& r = d_rows[it.d_rowId];
      TheoryVar s = r.getBaseVar();
      if (s != s_nullTheoryVar && isBase(s))
      {
        result += isNonFree(s);
        if (result > bestSoFar)
        {
          return result;
        }
      }
    }
  }
  return result;
}

TheoryVar TheoryArith::selectBlandsPivotCore(TheoryVar xI,
                                             bool isBelow,
                                             Numeral& outAIJ)
{
  Assert(isBase(xI));
  TheoryVar max = static_cast<TheoryVar>(getNumVars());
  TheoryVar result = max;
  const Row& r = d_rows[getVarRow(xI)];

  for (const RowEntry& it : r.d_entries)
  {
    if (!it.isDead())
    {
      TheoryVar xJ = it.d_var;
      const Numeral& aIJ = it.d_coeff;
      bool isNegC = isBelow ? isNeg(aIJ) : isPos(aIJ);
      bool isPosC = !isNegC;
      if (xI != xJ
          && ((isPosC && aboveLower(xJ)) || (isNegC && belowUpper(xJ))))
      {
        Assert(isNonBase(xJ));
        if (xJ < result)
        {
          result = xJ;
          outAIJ = aIJ;
        }
      }
    }
  }
  return result < max ? result : s_nullTheoryVar;
}

template <bool isBelow>
TheoryVar TheoryArith::selectPivotCore(TheoryVar xI, Numeral& outAIJ)
{
  Assert(isBase(xI));
  TheoryVar max = static_cast<TheoryVar>(getNumVars());
  TheoryVar result = max;
  const Row& r = d_rows[getVarRow(xI)];
  int bestColSz = INT_MAX;
  int bestSoFar = INT_MAX;
  int n = 0;

  for (const RowEntry& it : r.d_entries)
  {
    if (!it.isDead())
    {
      TheoryVar xJ = it.d_var;
      const Numeral& aIJ = it.d_coeff;

      bool isNegC = isBelow ? isNeg(aIJ) : isPos(aIJ);
      bool isPosC = !isNegC;
      if (xI != xJ
          && ((isPosC && aboveLower(xJ)) || (isNegC && belowUpper(xJ))))
      {
        int num = getNumNonFreeDepVars(xJ, bestSoFar);
        int colSz = static_cast<int>(d_columns[xJ].size());
        if (num < bestSoFar || (num == bestSoFar && colSz < bestColSz))
        {
          result = xJ;
          outAIJ = aIJ;
          bestSoFar = num;
          bestColSz = colSz;
          n = 1;
        }
        else if (num == bestSoFar && colSz == bestColSz)
        {
          n++;
          if (static_cast<unsigned>(d_random()) % static_cast<unsigned>(n)
              == 0)
          {
            result = xJ;
            outAIJ = aIJ;
          }
        }
      }
    }
  }
  return result < max ? result : s_nullTheoryVar;
}

LBool TheoryArith::getPhase(BoolVar bv)
{
  Atom* a = getBv2a(bv);
  if (a == nullptr)
  {
    // Not in Z3, which assumes an atom: an is_int atom has none.
    return L_UNDEF;
  }
  TheoryVar v = a->getVar();
  const InfNumeral& k = a->getK();
  switch (a->getBoundKind())
  {
    case B_LOWER: return getValue(v) >= k ? L_TRUE : L_FALSE;
    case B_UPPER: return getValue(v) <= k ? L_TRUE : L_FALSE;
    default: return L_UNDEF;
  }
}

TheoryVar TheoryArith::selectPivot(TheoryVar xI, bool isBelow, Numeral& outAIJ)
{
  if (d_blandsRule)
  {
    return selectBlandsPivotCore(xI, isBelow, outAIJ);
  }
  else if (isBelow)
  {
    return selectPivotCore<true>(xI, outAIJ);
  }
  else
  {
    return selectPivotCore<false>(xI, outAIJ);
  }
}

// ---------------------------------------------------------------------------
// Make feasible
// ---------------------------------------------------------------------------

bool TheoryArith::makeVarFeasible(TheoryVar xI)
{
  Assert(isBase(xI));

  bool isBelow;
  if (belowLower(xI))
  {
    isBelow = true;
  }
  else if (aboveUpper(xI))
  {
    isBelow = false;
  }
  else
  {
    // xI is already feasible
    return true;
  }

  Numeral aIJ;
  TheoryVar xJ = selectPivot(xI, isBelow, aIJ);
  if (xJ != s_nullTheoryVar)
  {
    Assert(isBase(xI));
    updateAndPivot(xI, xJ, aIJ, getBound(xI, !isBelow)->getValue());
    return true;
  }
  // conflict detected
  signRowConflict(xI, isBelow);
  return false;
}

TheoryVar TheoryArith::selectLgErrorVar(bool least)
{
  TheoryVar best = s_nullTheoryVar;
  InfNumeral bestError;
  InfNumeral currError;
  for (int v : d_toPatch)
  {
    if (belowLower(v))
    {
      currError = lower(v)->getValue() - getValue(v);
    }
    else if (aboveUpper(v))
    {
      currError = getValue(v) - upper(v)->getValue();
    }
    else
    {
      continue;
    }
    Assert(currError > InfNumeral(0));
    if (best == s_nullTheoryVar || (!least && currError > bestError)
        || (least && currError < bestError))
    {
      best = v;
      bestError = currError;
    }
  }
  if (best == s_nullTheoryVar)
  {
    d_toPatch.clear();  // all variables are satisfied
  }
  else
  {
    d_toPatch.erase(best);
  }
  return best;
}

TheoryVar TheoryArith::selectSmallestVar() { return d_toPatch.eraseMin(); }

TheoryVar TheoryArith::selectVarToFix()
{
  if (d_blandsRule)
  {
    return selectSmallestVar();
  }
  switch (d_params.d_arithPivotStrategy)
  {
    case ARITH_PIVOT_GREATEST_ERROR: return selectGreatestErrorVar();
    case ARITH_PIVOT_LEAST_ERROR: return selectLeastErrorVar();
    default: return selectSmallestVar();
  }
}

bool TheoryArith::makeFeasible()
{
  d_leftBasis.reset();
  d_blandsRule = false;
  size_t numRepeated = 0;
  while (!d_toPatch.empty())
  {
    TheoryVar v = selectVarToFix();
    if (v == s_nullTheoryVar)
    {
      // all variables were satisfied...
      Assert(d_toPatch.empty());
      break;
    }
    if (!d_blandsRule)
    {
      if (d_leftBasis.contains(v))
      {
        numRepeated++;
        if (numRepeated > blandsRuleThreshold())
        {
          d_blandsRule = true;
        }
      }
      else
      {
        d_leftBasis.insert(v);
      }
    }
    if (!makeVarFeasible(v))
    {
      return false;
    }
    if (d_ctx.getCancelFlag())
    {
      return true;
    }
  }
  return true;
}

void TheoryArith::signRowConflict(TheoryVar xI, bool isBelow)
{
  InfNumeral delta;
  const Row& r = d_rows[getVarRow(xI)];
  int idx = r.getIdxOf(xI);
  Assert(idx >= 0);
  Bound* b = nullptr;

  // Remark: if xI is an integer variable, then delta can be negative.
  if (isBelow)
  {
    Assert(belowLower(xI));
    b = lower(xI);
    if (relaxBounds())
    {
      delta = b->getValue();
      delta -= getValue(xI);
      delta -= getEpsilon(xI);
      if (delta.isNeg())
      {
        delta.reset();
      }
    }
  }
  else
  {
    Assert(aboveUpper(xI));
    b = upper(xI);
    if (relaxBounds())
    {
      delta = getValue(xI);
      delta -= b->getValue();
      delta -= getEpsilon(xI);
      if (delta.isNeg())
      {
        delta.reset();
      }
    }
  }

  Antecedents ante(*this);
  explainBound(r, idx, !isBelow, delta, ante);
  b->pushJustification(ante, Rational(1), coeffsEnabled());

  setConflict(ante, ante, "farkas");
}

// ---------------------------------------------------------------------------
// Assert bound
// ---------------------------------------------------------------------------

bool TheoryArith::assertLower(Bound* b)
{
  Assert(b->getBoundKind() == B_LOWER);
  TheoryVar v = b->getVar();
  const InfNumeral& k = b->getValue();

  Bound* u = upper(v);
  Bound* l = lower(v);

  if (u && k > u->getValue())
  {
    signBoundConflict(u, b);
    return false;
  }

  if (l && k <= l->getValue())
  {
    // redundant
    return true;
  }

  switch (getVarKind(v))
  {
    case QUASI_BASE:
      quasiBaseRow2BaseRow(getVarRow(v));
      Assert(getVarKind(v) == BASE);
      [[fallthrough]];
    case BASE:
      if (!d_toPatch.contains(v) && getValue(v) < k)
      {
        d_toPatch.insert(v);
      }
      break;
    case NON_BASE:
      if (getValue(v) < k)
      {
        setValue(v, k);
      }
      break;
  }

  pushBoundTrail(v, l, false);
  setBound(b, false);

  if (propagationMode() != BP_NONE)
  {
    addColumnRowsToTouchedRows(v);
  }

  return true;
}

bool TheoryArith::assertUpper(Bound* b)
{
  Assert(b->getBoundKind() == B_UPPER);
  TheoryVar v = b->getVar();
  const InfNumeral& k = b->getValue();

  Bound* u = upper(v);
  Bound* l = lower(v);

  if (l && k < l->getValue())
  {
    signBoundConflict(l, b);
    return false;
  }

  if (u && k >= u->getValue())
  {
    // redundant
    return true;
  }

  switch (getVarKind(v))
  {
    case QUASI_BASE:
      quasiBaseRow2BaseRow(getVarRow(v));
      Assert(getVarKind(v) == BASE);
      [[fallthrough]];
    case BASE:
      if (!d_toPatch.contains(v) && getValue(v) > k)
      {
        d_toPatch.insert(v);
      }
      break;
    case NON_BASE:
      if (getValue(v) > k)
      {
        setValue(v, k);
      }
      break;
  }

  pushBoundTrail(v, u, true);
  setBound(b, true);

  if (propagationMode() != BP_NONE)
  {
    addColumnRowsToTouchedRows(v);
  }

  return true;
}

bool TheoryArith::assertBound(Bound* b)
{
  TheoryVar v = b->getVar();

  if (b->isAtom())
  {
    Assert(d_unassignedAtoms[v] > 0);
    pushDecUnassignedAtomsTrail(v);
    d_unassignedAtoms[v]--;
  }

  bool result = true;
  switch (b->getBoundKind())
  {
    case B_LOWER:
      d_stats.d_assertLower++;
      result = assertLower(b);
      break;
    case B_UPPER:
      d_stats.d_assertUpper++;
      result = assertUpper(b);
      break;
  }

  return result;
}

void TheoryArith::signBoundConflict(Bound* b1, Bound* b2)
{
  Assert(b1->getVar() == b2->getVar());
  Antecedents ante(*this);
  b1->pushJustification(ante, Rational(1), coeffsEnabled());
  b2->pushJustification(ante, Rational(1), coeffsEnabled());
  setConflict(ante, ante, "farkas");
}

// ---------------------------------------------------------------------------
// Bound propagation
// ---------------------------------------------------------------------------

void TheoryArith::markRowForBoundProp(size_t r1)
{
  if (!d_inToCheck.contains(r1) && d_rows[r1].d_baseVar != s_nullTheoryVar)
  {
    d_inToCheck.insert(r1);
    d_toCheck.push_back(r1);
  }
}

void TheoryArith::addColumnRowsToTouchedRows(TheoryVar v)
{
  for (const ColEntry& ce : d_columns[v])
  {
    if (!ce.isDead())
    {
      markRowForBoundProp(ce.d_rowId);
    }
  }
}

void TheoryArith::isRowUsefulForBoundProp(const Row& r,
                                          int& lowerIdx,
                                          int& upperIdx) const
{
  lowerIdx = -1;
  upperIdx = -1;
  int i = 0;
  for (auto it = r.begin(), end = r.end(); it != end; ++it, ++i)
  {
    if (!it->isDead())
    {
      if (skipBigCoeffs() && isBig(it->d_coeff))
      {
        lowerIdx = -2;
        upperIdx = -2;
        return;
      }
      bool isPosC = isPos(it->d_coeff);
      if (lower(it->d_var) == nullptr)
      {
        if (isPosC)
        {
          upperIdx = upperIdx == -1 ? i : -2;
        }
        else
        {
          lowerIdx = lowerIdx == -1 ? i : -2;
        }
      }
      if (upper(it->d_var) == nullptr)
      {
        if (isPosC)
        {
          lowerIdx = lowerIdx == -1 ? i : -2;
        }
        else
        {
          upperIdx = upperIdx == -1 ? i : -2;
        }
      }
      if (lowerIdx == -2 && upperIdx == -2)
      {
        return;
      }
    }
  }
}

size_t TheoryArith::implyBoundForMonomial(const Row& r, int idx, bool isLower)
{
  const RowEntry& entry = r[idx];
  size_t count = 0;
  if (d_unassignedAtoms[entry.d_var] > 0)
  {
    InfNumeral impliedK;
    int idx2 = 0;
    for (auto it = r.begin(), end = r.end(); it != end; ++it, ++idx2)
    {
      if (!it->isDead() && idx != idx2)
      {
        Bound* b = getBound(
            it->d_var, isLower ? isPos(it->d_coeff) : isNeg(it->d_coeff));
        Assert(b);
        impliedK.submul(it->d_coeff, b->getValue());
      }
    }
    impliedK /= entry.d_coeff;
    if (isPos(entry.d_coeff) == isLower)
    {
      // impliedK is a lower bound for entry.d_var
      Bound* curr = lower(entry.d_var);
      if (curr == nullptr || impliedK > curr->getValue())
      {
        count += mkImpliedBound(r, idx, isLower, entry.d_var, B_LOWER, impliedK);
      }
    }
    else
    {
      // impliedK is an upper bound for entry.d_var
      Bound* curr = upper(entry.d_var);
      if (curr == nullptr || impliedK < curr->getValue())
      {
        count += mkImpliedBound(r, idx, isLower, entry.d_var, B_UPPER, impliedK);
      }
    }
  }
  return count;
}

size_t TheoryArith::implyBoundForAllMonomials(const Row& r, bool isLower)
{
  // Traverse the row once and compute
  // bb = (Sum_{a_i < 0} -a_i*lower(x_i)) + (Sum_{a_j > 0} -a_j * upper(x_j))
  //   if isLower = true
  // bb = (Sum_{a_i > 0} -a_i*lower(x_i)) + (Sum_{a_j < 0} -a_j * upper(x_j))
  //   if isLower = false
  InfNumeral bb;
  for (const RowEntry& re : r)
  {
    if (!re.isDead())
    {
      const InfNumeral& b =
          getBound(re.d_var, isLower ? isPos(re.d_coeff) : isNeg(re.d_coeff))
              ->getValue();
      bb.submul(re.d_coeff, b);
    }
  }

  size_t count = 0;
  InfNumeral impliedK;
  int idx = 0;
  for (auto it = r.begin(), end = r.end(); it != end; ++it, ++idx)
  {
    if (!it->isDead() && d_unassignedAtoms[it->d_var] > 0)
    {
      const InfNumeral& b =
          getBound(it->d_var, isLower ? isPos(it->d_coeff) : isNeg(it->d_coeff))
              ->getValue();
      impliedK = bb;
      impliedK.addmul(it->d_coeff, b);
      // impliedK is a bound for the monomial in position it
      impliedK /= it->d_coeff;
      if (isPos(it->d_coeff) == isLower)
      {
        // impliedK is a lower bound for it->d_var
        Bound* curr = lower(it->d_var);
        if (curr == nullptr || impliedK > curr->getValue())
        {
          // improved lower bound
          count += mkImpliedBound(r, idx, isLower, it->d_var, B_LOWER, impliedK);
        }
      }
      else
      {
        // impliedK is an upper bound for it->d_var
        Bound* curr = upper(it->d_var);
        if (curr == nullptr || impliedK < curr->getValue())
        {
          // improved upper bound
          count += mkImpliedBound(r, idx, isLower, it->d_var, B_UPPER, impliedK);
        }
      }
    }
  }
  return count;
}

void TheoryArith::explainBound(const Row& r,
                               int idx,
                               bool isLower,
                               InfNumeral& delta,
                               Antecedents& ante)
{
  Assert(delta >= InfNumeral());

  if (!relaxBounds() && (!ante.lits().empty() || !ante.eqs().empty()))
  {
    return;
  }
  const RowEntry& entry = r[idx];
  Numeral coeff = entry.d_coeff;
  if (relaxBounds())
  {
    // if the variable v at position idx can have a delta increase (decrease)
    // of 'delta', then the monomial (coeff * v) at position idx can have a
    // delta increase (decrease) of '|coeff| * delta'
    if (isNeg(coeff))
    {
      coeff = -coeff;
    }
    delta *= coeff;  // adjust delta
  }
  int idx2 = 0;
  for (auto it = r.begin(), end = r.end(); it != end; ++it, ++idx2)
  {
    if (!it->isDead() && idx != idx2)
    {
      Bound* b = getBound(it->d_var,
                          isLower ? isPos(it->d_coeff) : isNeg(it->d_coeff));
      Assert(b);
      if (!b->hasJustification())
      {
        continue;
      }
      if (!relaxBounds() || delta.isZero())
      {
        b->pushJustification(ante, it->d_coeff, coeffsEnabled());
        continue;
      }
      Numeral coeff2 = it->d_coeff;
      bool isBLower = b->getBoundKind() == B_LOWER;
      if (isNeg(coeff2))
      {
        coeff2 = -coeff2;
      }
      Numeral invCoeff(1);
      invCoeff /= coeff2;
      InfNumeral k1 = b->getValue();
      InfNumeral limitK1;
      // if the max decrease (increase) of the curr monomial (coeff * v2) is
      // delta, then the maximal decrease (increase) of v2 is
      // (1/|coeff| * delta)
      if (isBLower)
      {
        limitK1 = k1;
        limitK1.submul(invCoeff, delta);
      }
      else
      {
        limitK1 = k1;
        limitK1.addmul(invCoeff, delta);
      }
      InfNumeral k2 = k1;
      Atom* newAtom = nullptr;
      const Atoms& as = d_varOccs[it->d_var];
      for (Atom* a : as)
      {
        if (a == b)
        {
          continue;
        }
        BoolVar bv = a->getBoolVar();
        LBool val = d_ctx.getAssignment(bv);
        if (val == L_UNDEF)
        {
          continue;
        }
        a->assignEh(val == L_TRUE, getEpsilon(a->getVar()));
        if (val != L_UNDEF && a->getBoundKind() == b->getBoundKind())
        {
          Assert((d_ctx.getAssignment(bv) == L_TRUE) == a->isTrue());
          InfNumeral aVal = a->getValue();
          if (isBLower)
          {
            if (aVal >= limitK1 && aVal < k2)
            {
              k2 = aVal;
              newAtom = a;
            }
          }
          else
          {
            if (aVal <= limitK1 && aVal > k2)
            {
              k2 = aVal;
              newAtom = a;
            }
          }
        }
      }
      Assert(!isBLower || k2 <= k1);
      Assert(isBLower || k2 >= k1);
      if (newAtom == nullptr)
      {
        b->pushJustification(ante, coeff2, coeffsEnabled());
        continue;
      }
      if (isBLower)
      {
        delta -= coeff2 * (k1 - k2);
      }
      else
      {
        delta -= coeff2 * (k2 - k1);
      }
      newAtom->pushJustification(ante, coeff2, coeffsEnabled());
      Assert(delta >= InfNumeral());
    }
  }
}

size_t TheoryArith::mkImpliedBound(const Row& r,
                                   size_t idx,
                                   bool isLower,
                                   TheoryVar v,
                                   BoundKind kind,
                                   const InfNumeral& k)
{
  const Atoms& as = d_varOccs[v];
  const InfNumeral& epsilon = getEpsilon(v);
  InfNumeral delta;
  size_t count = 0;
  for (Atom* a : as)
  {
    BoolVar bv = a->getBoolVar();
    Literal l(bv);
    if (d_ctx.getAssignment(bv) == L_UNDEF)
    {
      const InfNumeral& k2 = a->getK();
      delta.reset();
      if (a->getAtomKind() == A_LOWER)
      {
        // v >= k  k >= k2  |-  v >= k2
        if (kind == B_LOWER && k >= k2)
        {
          if (relaxBounds())
          {
            delta = k;
            delta -= k2;
          }
          assignBoundLiteral(l, r, idx, isLower, delta);
          ++count;
        }
        // v <= k  k <  k2  |-  v < k2  |- not v >= k2
        if (kind == B_UPPER && k < k2)
        {
          // it is not sufficient to check whether k < k2, see Z3.
          delta = k2;
          delta -= k;
          delta -= epsilon;
          if (delta.isNonneg())
          {
            assignBoundLiteral(~l, r, idx, isLower, delta);
            ++count;
          }
        }
      }
      else
      {
        // v >= k  k > k2  |-  v > k2 |- not v <= k2
        if (kind == B_LOWER && k > k2)
        {
          // it is not sufficient to check whether k > k2.
          delta = k;
          delta -= k2;
          delta -= epsilon;
          if (delta.isNonneg())
          {
            assignBoundLiteral(~l, r, idx, isLower, delta);
            ++count;
          }
        }
        // v <= k  k <= k2 |-  v <= k2
        if (kind == B_UPPER && k <= k2)
        {
          if (relaxBounds())
          {
            delta = k2;
            delta -= k;
          }
          assignBoundLiteral(l, r, idx, isLower, delta);
          ++count;
        }
      }
    }
  }
  return count;
}

void TheoryArith::assignBoundLiteral(
    Literal l, const Row& r, size_t idx, bool isLower, InfNumeral& delta)
{
  d_stats.d_boundProps++;
  Antecedents ante(*this);
  explainBound(r, static_cast<int>(idx), isLower, delta, ante);

  if (ante.lits().size() < smallLemmaSize() && ante.eqs().empty())
  {
    LiteralVector& lits = d_tmpLiteralVector2;
    lits.clear();
    lits.push_back(l);
    for (const Literal& lit : ante.lits())
    {
      lits.push_back(~lit);
    }
    d_ctx.mkClause(lits.size(), lits.data(), nullptr, CLS_TH_LEMMA, nullptr);
  }
  else
  {
    d_ctx.assign(l,
                 d_ctx.mkJustification(ExtTheoryPropagationJustification(
                     getId(),
                     d_ctx,
                     ante.lits().size(),
                     ante.lits().data(),
                     ante.eqs().size(),
                     ante.eqs().data(),
                     l)));
  }
}

void TheoryArith::propagateBounds()
{
  size_t count = 0;
  // Z3 iterates m_to_check with a range-for.
  for (size_t i = 0, sz = d_toCheck.size(); i < sz; ++i)
  {
    size_t rIdx = d_toCheck[i];
    Row& r = d_rows[rIdx];
    if (r.getBaseVar() != s_nullTheoryVar)
    {
      if (r.size() < maxLemmaSize())
      {  // Ignore big rows.
        int lowerIdx;
        int upperIdx;
        isRowUsefulForBoundProp(r, lowerIdx, upperIdx);

        if (lowerIdx >= 0)
        {
          count += implyBoundForMonomial(r, lowerIdx, true);
        }
        else if (lowerIdx == -1)
        {
          count += implyBoundForAllMonomials(r, true);
        }

        if (upperIdx >= 0)
        {
          count += implyBoundForMonomial(r, upperIdx, false);
        }
        else if (upperIdx == -1)
        {
          count += implyBoundForAllMonomials(r, false);
        }

        // sneaking cheap eq detection in this loop
        propagateCheapEq(rIdx);
      }
    }
  }
  (void)count;

  d_toCheck.clear();
  d_inToCheck.reset();
}

// ---------------------------------------------------------------------------
// Justification
// ---------------------------------------------------------------------------

void TheoryArith::setConflict(const Antecedents& ante,
                              Antecedents& bounds,
                              const char* proofRule)
{
  setConflict(ante.lits().size(),
              ante.lits().data(),
              ante.eqs().size(),
              ante.eqs().data(),
              bounds,
              proofRule);
}

void TheoryArith::setConflict(const DerivedBound& ante,
                              Antecedents& bounds,
                              const char* proofRule)
{
  setConflict(ante.lits().size(),
              ante.lits().data(),
              ante.eqs().size(),
              ante.eqs().data(),
              bounds,
              proofRule);
}

void TheoryArith::setConflict(size_t numLiterals,
                              const Literal* lits,
                              size_t numEqs,
                              const ENodePair* eqs,
                              Antecedents& /*bounds*/,
                              const char* /*proofRule*/)
{
  Assert(numLiterals != 0 || numEqs != 0);
  d_stats.d_conflicts++;
  d_numConflicts++;
  // record_conflict belongs to theory_opt, which is not ported.
  d_ctx.setConflict(d_ctx.mkJustification(ExtTheoryConflictJustification(
      getId(), d_ctx, numLiterals, lits, numEqs, eqs)));
}

void TheoryArith::collectFixedVarJustifications(const Row& r,
                                                Antecedents& antecedents) const
{
  for (const RowEntry& re : r)
  {
    if (!re.isDead() && isFixed(re.d_var))
    {
      lower(re.d_var)->pushJustification(
          antecedents, re.d_coeff, coeffsEnabled());
      upper(re.d_var)->pushJustification(
          antecedents, re.d_coeff, coeffsEnabled());
    }
  }
}

// ---------------------------------------------------------------------------
// Model generation
// ---------------------------------------------------------------------------

void TheoryArith::updateEpsilon(const InfNumeral& l, const InfNumeral& u)
{
  if (l.getRational() < u.getRational()
      && l.getInfinitesimal() > u.getInfinitesimal())
  {
    Numeral newEpsilon = (u.getRational() - l.getRational())
                         / (l.getInfinitesimal() - u.getInfinitesimal());
    if (newEpsilon < d_epsilon)
    {
      d_epsilon = newEpsilon;
    }
  }
  Assert(isPos(d_epsilon));
}

void TheoryArith::computeEpsilon()
{
  // Z3 param m_arith_epsilon (arith.epsilon, default 1.0)
  d_epsilon = Rational(d_params.d_arithEpsilonNum);
  TheoryVar num = static_cast<TheoryVar>(getNumVars());
  for (TheoryVar v = 0; v < num; ++v)
  {
    Bound* l = lower(v);
    Bound* u = upper(v);
    if (l != nullptr)
    {
      updateEpsilon(l->getValue(), getValue(v));
    }
    if (u != nullptr)
    {
      updateEpsilon(getValue(v), u->getValue());
    }
  }
}

void TheoryArith::refineEpsilon()
{
  while (true)
  {
    // rational2var: only used for lookups
    std::map<Rational, TheoryVar> mapping;
    TheoryVar num = static_cast<TheoryVar>(getNumVars());
    bool refine = false;
    for (TheoryVar v = 0; v < num; ++v)
    {
      if (isIntSrc(v))
      {
        continue;
      }
      if (!d_ctx.isShared(getENode(v)))
      {
        continue;
      }
      const InfNumeral& val = getValue(v);
      if (isInfinite(val))
      {
        continue;
      }
      Rational value =
          val.getRational() + d_epsilon * val.getInfinitesimal();
      auto it = mapping.find(value);
      if (it != mapping.end())
      {
        TheoryVar v2 = it->second;
        Assert(!isIntSrc(v2));
        if (getValue(v) != getValue(v2))
        {
          // v and v2 are not known to be equal. The choice of d_epsilon is
          // making them equal.
          refine = true;
          break;
        }
      }
      else
      {
        mapping.emplace(value, v);
      }
    }
    if (!refine)
    {
      return;
    }
    Numeral two(2);
    d_epsilon = d_epsilon / two;
  }
}

bool TheoryArith::getModelValue(ENode* n, Node& r)
{
  // Z3's mk_value
  TheoryVar v = n->getThVar(getId());
  if (v == s_nullTheoryVar)
  {
    return false;
  }
  const InfNumeral& val = getValue(v);
  Rational num = val.getRational() + d_epsilon * val.getInfinitesimal();
  if (isInt(v) && !num.isIntegral())
  {
    // Truncating non-integer value; possible for non-linear constraints.
    num = floor(num);
  }
  r = NodeManager::mkConstRealOrInt(n->getExpr().getType(), num);
  return true;
}

bool TheoryArith::getValue(ENode* n, Node& r)
{
  TheoryVar v = n->getThVar(getId());
  if (v == s_nullTheoryVar)
  {
    return false;
  }
  InfNumeral val = getValue(v);
  if (isInt(v) && !val.isInt())
  {
    return false;
  }
  // to_expr: only a value without infinitesimal has an expression.
  if (!val.getInfinitesimal().isZero())
  {
    return false;
  }
  r = NodeManager::mkConstRealOrInt(n->getExpr().getType(), val.getRational());
  return true;
}

// ---------------------------------------------------------------------------
// Backtracking
// ---------------------------------------------------------------------------

void TheoryArith::pushScopeEh()
{
  Theory::pushScopeEh();
  d_scopes.push_back(Scope());
  Scope& s = d_scopes.back();
  s.d_atomsLim = d_atoms.size();
  s.d_boundTrailLim = d_boundTrail.size();
  s.d_unassignedAtomsTrailLim = d_unassignedAtomsTrail.size();
  s.d_assertedBoundsLim = d_assertedBounds.size();
  s.d_assertedQheadOld = d_assertedQhead;
  s.d_boundsToDeleteLim = d_boundsToDelete.size();
  s.d_nlMonomialsLim = d_nlMonomials.size();
  s.d_nlPropagatedLim = d_nlPropagated.size();
}

void TheoryArith::popScopeEh(size_t numScopes)
{
  // The update trail stack may not be empty (quasiBaseRow2BaseRow inserts
  // into it), so the assignment must be restored.
  restoreAssignment();
  d_toPatch.reset();
  size_t lvl = d_scopes.size();
  Assert(numScopes <= lvl);
  size_t newLvl = lvl - numScopes;
  Scope& s = d_scopes[newLvl];
  restoreBounds(s.d_boundTrailLim);
  restoreUnassignedAtoms(s.d_unassignedAtomsTrailLim);
  d_assertedBounds.resize(s.d_assertedBoundsLim);
  d_assertedQhead = s.d_assertedQheadOld;
  restoreNlPropagatedFlag(s.d_nlPropagatedLim);
  d_nlMonomials.resize(s.d_nlMonomialsLim);
  delAtoms(s.d_atomsLim);
  delBounds(s.d_boundsToDeleteLim);
  delVars(getOldNumVars(numScopes));
  d_scopes.resize(newLvl);
  Theory::popScopeEh(numScopes);
  bool ok = makeFeasible();
  AlwaysAssert(ok);
  Assert(d_toPatch.empty());
  d_toCheck.clear();
  d_inToCheck.reset();
  d_newAtoms.clear();
}

void TheoryArith::restoreNlPropagatedFlag(size_t oldTrailSize)
{
  size_t i = d_nlPropagated.size();
  while (i != oldTrailSize)
  {
    --i;
    Assert(d_data[d_nlPropagated[i]].d_nlPropagated);
    d_data[d_nlPropagated[i]].d_nlPropagated = false;
  }
  d_nlPropagated.resize(oldTrailSize);
}

void TheoryArith::restoreBounds(size_t oldTrailSize)
{
  size_t i = d_boundTrail.size();
  while (i != oldTrailSize)
  {
    --i;
    const BoundTrail& t = d_boundTrail[i];
    TheoryVar v = t.getVar();
    Bound* b = t.getOldBound();
    Assert(isBase(v) || isNonBase(v));
    restoreBound(v, b, t.isUpper());
    if (lazyPivotingLvl() > 2 && b == nullptr && isBase(v) && isFree(v))
    {
      eliminate<false>(v, false);
      Assert(d_columns[v].size() == 1);
      setVarKind(v, QUASI_BASE);
    }
  }
  d_boundTrail.erase(d_boundTrail.begin() + oldTrailSize, d_boundTrail.end());
}

void TheoryArith::restoreUnassignedAtoms(size_t oldTrailSize)
{
  size_t i = d_unassignedAtomsTrail.size();
  while (i != oldTrailSize)
  {
    --i;
    d_unassignedAtoms[d_unassignedAtomsTrail[i]]++;
  }
  d_unassignedAtomsTrail.resize(oldTrailSize);
}

void TheoryArith::delAtoms(size_t oldSize)
{
  size_t i = d_atoms.size();
  while (i != oldSize)
  {
    --i;
    Atom* a = d_atoms[i];
    TheoryVar v = a->getVar();
    BoolVar bv = a->getBoolVar();
    eraseBv2a(bv);
    Assert(d_varOccs[v].back() == a);
    d_varOccs[v].pop_back();
    delete a;
  }
  d_atoms.resize(oldSize);
}

void TheoryArith::delBounds(size_t oldSize)
{
  size_t i = d_boundsToDelete.size();
  while (i != oldSize)
  {
    --i;
    delete d_boundsToDelete[i];
  }
  d_boundsToDelete.resize(oldSize);
}

void TheoryArith::delVars(size_t oldNumVars)
{
  int numVars = static_cast<int>(getNumVars());
  Assert(numVars >= static_cast<int>(oldNumVars));
  if (numVars != static_cast<int>(oldNumVars))
  {
    TheoryVar v = numVars;
    while (v > static_cast<int>(oldNumVars))
    {
      --v;
      switch (getVarKind(v))
      {
        case QUASI_BASE:
          Assert(d_columns[v].size() == 1);
          delRow(getVarRow(v));
          break;
        case BASE:
          Assert(lazyPivotingLvl() != 0 || d_columns[v].size() == 1);
          if (lazyPivotingLvl() > 0)
          {
            eliminate<false>(v, false);
          }
          delRow(getVarRow(v));
          break;
        case NON_BASE:
        {
          const ColEntry* entry = getABaseRowThatContains(v);
          if (entry)
          {
            Row& r = d_rows[entry->d_rowId];
            Assert(isBase(r.getBaseVar()));
            Assert(r[entry->d_rowIdx].d_var == v);
            // copy: the row is modified by the pivot
            Numeral coeff = r[entry->d_rowIdx].d_coeff;
            pivot<false>(r.getBaseVar(), v, coeff, false);
            Assert(isBase(v));
            delRow(getVarRow(v));
          }
          break;
        }
      }
      d_inUpdateTrailStack.remove(v);
      d_leftBasis.remove(v);
      d_inToCheck.remove(v);
    }
    d_columns.resize(oldNumVars);
    d_data.resize(oldNumVars);
    d_value.resize(oldNumVars);
    d_oldValue.resize(oldNumVars);
    d_varOccs.resize(oldNumVars);
    d_unassignedAtoms.resize(oldNumVars);
    d_varPos.resize(oldNumVars);
    d_bounds[0].resize(oldNumVars);
    d_bounds[1].resize(oldNumVars);
  }
  Assert(d_varOccs.size() == oldNumVars);
}

void TheoryArith::delRow(size_t rId)
{
  Row& r = d_rows[rId];
  for (const RowEntry& re : r)
  {
    if (!re.isDead())
    {
      Column& c = d_columns[re.d_var];
      c.delColEntry(re.d_colIdx);
    }
  }
  r.d_baseVar = s_nullTheoryVar;
  r.reset();
  d_deadRows.push_back(rId);
}

// ---------------------------------------------------------------------------
// Inline definitions of Z3's theory_arith.h
// ---------------------------------------------------------------------------

bool TheoryArith::hasVar(TNode v) const
{
  return d_ctx.eInternalized(v)
         && d_ctx.getENode(v)->getThVar(getId()) != s_nullTheoryVar;
}

TheoryVar TheoryArith::expr2var(TNode v) const
{
  Assert(d_ctx.eInternalized(v));
  return d_ctx.getENode(v)->getThVar(getId());
}

bool TheoryArith::isIntSrc(TheoryVar v) const
{
  return arith::isIntSort(var2expr(v));
}

bool TheoryArith::isFree(TNode n) const
{
  Assert(d_ctx.eInternalized(n)
         && d_ctx.getENode(n)->getThVar(getId()) != s_nullTheoryVar);
  return isFree(d_ctx.getENode(n)->getThVar(getId()));
}

Node TheoryArith::mkEqAtom(TNode lhs, TNode rhs)
{
  // m_util.mk_eq: a numeral goes on the right-hand side; otherwise the
  // left-hand side has the smaller id.
  if (arith::isNumeral(lhs)
      || (!arith::isNumeral(rhs) && lhs.getId() > rhs.getId()))
  {
    std::swap(lhs, rhs);
  }
  NodeManager* nm = d_ctx.getEnv().getNodeManager();
  if (lhs == rhs)
  {
    return nm->mkConst(true);
  }
  if (arith::isNumeral(lhs) && arith::isNumeral(rhs))
  {
    return nm->mkConst(false);
  }
  return nm->mkNode(Kind::EQUAL, lhs, rhs);
}

// ---------------------------------------------------------------------------
// Explicit instantiations
// ---------------------------------------------------------------------------

template void TheoryArith::addRowEntry<false>(size_t,
                                              const Numeral&,
                                              TheoryVar);
template void TheoryArith::addRowEntry<true>(size_t,
                                             const Numeral&,
                                             TheoryVar);
template void TheoryArith::pivot<false>(TheoryVar,
                                        TheoryVar,
                                        const Numeral&,
                                        bool);
template void TheoryArith::pivot<true>(TheoryVar,
                                       TheoryVar,
                                       const Numeral&,
                                       bool);
template void TheoryArith::eliminate<false>(TheoryVar, bool);
template void TheoryArith::eliminate<true>(TheoryVar, bool);
template TheoryVar TheoryArith::selectPivotCore<false>(TheoryVar, Numeral&);
template TheoryVar TheoryArith::selectPivotCore<true>(TheoryVar, Numeral&);

}  // namespace z3
}  // namespace cvc5::internal
