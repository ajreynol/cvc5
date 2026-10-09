/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The recognizers and constructors of Z3's arith_util, over cvc5 nodes.
 *
 * Not from Z3: this maps the arithmetic function symbols Z3's theory_arith
 * tests for onto cvc5's kinds. The terms reach the core after cvc5's rewriter,
 * whose normal form differs from Z3's -- (>= t k) and (not (>= t k)) rather
 * than Z3's (<= t k) and (>= t k), MULT for a numeral times a term and
 * NONLINEAR_MULT for a product of terms, the total versions of the division
 * operators -- so a recognizer accepts every form either side produces.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__ARITH_UTIL_H
#define CVC5__Z3__ARITH_UTIL_H

#include "expr/node.h"
#include "expr/node_manager.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace z3 {
namespace arith {

/** m_util.is_numeral(n, val) */
inline bool isNumeral(TNode n, Rational& val)
{
  if (n.getKind() == Kind::CONST_RATIONAL || n.getKind() == Kind::CONST_INTEGER)
  {
    val = n.getConst<Rational>();
    return true;
  }
  if (n.getKind() == Kind::TO_REAL
      && (n[0].getKind() == Kind::CONST_INTEGER
          || n[0].getKind() == Kind::CONST_RATIONAL))
  {
    val = n[0].getConst<Rational>();
    return true;
  }
  return false;
}

inline bool isNumeral(TNode n)
{
  Rational val;
  return isNumeral(n, val);
}

/** True for a term of an arithmetic sort. */
inline bool isArith(TNode n) { return n.getType().isRealOrInt(); }

/** m_util.is_int(n) */
inline bool isIntSort(TNode n) { return n.getType().isInteger(); }

inline bool isAdd(TNode n) { return n.getKind() == Kind::ADD; }
inline bool isSub(TNode n) { return n.getKind() == Kind::SUB; }
inline bool isUminus(TNode n) { return n.getKind() == Kind::NEG; }
/** Both a numeral times a term (MULT) and a product of terms. */
inline bool isMul(TNode n)
{
  return n.getKind() == Kind::MULT || n.getKind() == Kind::NONLINEAR_MULT;
}
inline bool isDiv(TNode n)
{
  return n.getKind() == Kind::DIVISION || n.getKind() == Kind::DIVISION_TOTAL;
}
inline bool isIdiv(TNode n)
{
  return n.getKind() == Kind::INTS_DIVISION
         || n.getKind() == Kind::INTS_DIVISION_TOTAL;
}
inline bool isMod(TNode n)
{
  return n.getKind() == Kind::INTS_MODULUS
         || n.getKind() == Kind::INTS_MODULUS_TOTAL;
}
/** The total versions, whose value at a zero divisor is fixed. */
inline bool isTotalDivOp(TNode n)
{
  return n.getKind() == Kind::DIVISION_TOTAL
         || n.getKind() == Kind::INTS_DIVISION_TOTAL
         || n.getKind() == Kind::INTS_MODULUS_TOTAL;
}
inline bool isToReal(TNode n) { return n.getKind() == Kind::TO_REAL; }
inline bool isToInt(TNode n) { return n.getKind() == Kind::TO_INTEGER; }
inline bool isIsInt(TNode n) { return n.getKind() == Kind::IS_INTEGER; }
inline bool isLe(TNode n) { return n.getKind() == Kind::LEQ; }
inline bool isGe(TNode n) { return n.getKind() == Kind::GEQ; }
inline bool isLt(TNode n) { return n.getKind() == Kind::LT; }
inline bool isGt(TNode n) { return n.getKind() == Kind::GT; }

/** m_util.mk_numeral(val, is_int) */
inline Node mkNumeral(NodeManager* nm, const Rational& val, bool isInt)
{
  return isInt ? nm->mkConstInt(val) : nm->mkConstReal(val);
}

inline Node mkLe(NodeManager* nm, TNode a, TNode b)
{
  return nm->mkNode(Kind::LEQ, a, b);
}
inline Node mkGe(NodeManager* nm, TNode a, TNode b)
{
  return nm->mkNode(Kind::GEQ, a, b);
}
inline Node mkMul(NodeManager* nm, TNode a, TNode b)
{
  return nm->mkNode(isNumeral(a) || isNumeral(b) ? Kind::MULT
                                                 : Kind::NONLINEAR_MULT,
                    a,
                    b);
}
inline Node mkAdd(NodeManager* nm, TNode a, TNode b)
{
  return nm->mkNode(Kind::ADD, a, b);
}
inline Node mkSub(NodeManager* nm, TNode a, TNode b)
{
  return nm->mkNode(Kind::SUB, a, b);
}

}  // namespace arith
}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__ARITH_UTIL_H */
