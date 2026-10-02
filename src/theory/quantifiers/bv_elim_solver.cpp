/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Solving bit-vector literals using elimination sets.
 */

#include "theory/quantifiers/bv_elim_solver.h"

#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

Node BvElimSolver::mkLowBit(Node a)
{
  return NodeManager::mkNode(
      Kind::BITVECTOR_AND, a, NodeManager::mkNode(Kind::BITVECTOR_NEG, a));
}

Node BvElimSolver::mkHighBit(Node a)
{
  NodeManager* nm = a.getNodeManager();
  uint32_t w = bv::utils::getSize(a);
  Node v = a;
  for (uint32_t k = 1; k < w; k *= 2)
  {
    v = NodeManager::mkNode(
        Kind::BITVECTOR_OR,
        v,
        NodeManager::mkNode(
            Kind::BITVECTOR_LSHR, v, bv::utils::mkConst(nm, w, k)));
  }
  return NodeManager::mkNode(
      Kind::BITVECTOR_XOR,
      v,
      NodeManager::mkNode(Kind::BITVECTOR_LSHR, v, bv::utils::mkOne(nm, w)));
}

Node BvElimSolver::mkOddInverse(Node a)
{
  NodeManager* nm = a.getNodeManager();
  uint32_t w = bv::utils::getSize(a);
  Node two = bv::utils::mkConst(nm, w, 2);
  // a * a = 1 mod 8 for odd a, hence a is correct on the 3 lowest bits, and
  // each Newton iteration doubles the number of correct bits
  Node y = a;
  for (uint32_t bits = 3; bits < w; bits *= 2)
  {
    y = NodeManager::mkNode(
        Kind::BITVECTOR_MULT,
        y,
        NodeManager::mkNode(Kind::BITVECTOR_SUB,
                            two,
                            NodeManager::mkNode(Kind::BITVECTOR_MULT, a, y)));
  }
  return y;
}

Node BvElimSolver::mkLog2(Node p)
{
  NodeManager* nm = p.getNodeManager();
  uint32_t w = bv::utils::getSize(p);
  // the number of bits required to represent w-1, which is at least one
  uint32_t nbits = 1;
  while (nbits < 32 && (static_cast<uint64_t>(1) << nbits) < w)
  {
    nbits++;
  }
  Assert(nbits <= w);
  // bit j of the result is set iff the set bit of p is at a position whose
  // index has its j^th bit set
  std::vector<Node> bits;
  if (nbits < w)
  {
    bits.push_back(bv::utils::mkZero(nm, w - nbits));
  }
  for (uint32_t j = nbits; j > 0; j--)
  {
    BitVector mask(w);
    for (uint32_t i = 0; i < w; i++)
    {
      if ((i >> (j - 1)) & 1)
      {
        mask.setBit(i, true);
      }
    }
    bits.push_back(NodeManager::mkNode(
        Kind::BITVECTOR_REDOR,
        NodeManager::mkNode(
            Kind::BITVECTOR_AND, p, bv::utils::mkConst(nm, mask))));
  }
  return bv::utils::mkConcat(bits);
}

bool BvElimSolver::getEqualityElimSet(Node svt,
                                      uint32_t index,
                                      Node t,
                                      std::vector<Node>& terms)
{
  NodeManager* nm = t.getNodeManager();
  Kind k = svt.getKind();
  size_t nchildren = svt.getNumChildren();
  Assert(index < nchildren);
  uint32_t w = bv::utils::getSize(svt[index]);
  if (k == Kind::BITVECTOR_CONCAT)
  {
    // x = t[upper:lower]
    uint32_t upper = bv::utils::getSize(t) - 1;
    uint32_t lower = 0;
    for (size_t i = 0; i < nchildren; i++)
    {
      if (i < index)
      {
        upper -= bv::utils::getSize(svt[i]);
      }
      else if (i > index)
      {
        lower += bv::utils::getSize(svt[i]);
      }
    }
    terms.push_back(bv::utils::mkExtract(t, upper, lower));
    return true;
  }
  else if (k == Kind::BITVECTOR_SIGN_EXTEND)
  {
    terms.push_back(bv::utils::mkExtract(t, w - 1, 0));
    return true;
  }
  else if (k == Kind::BITVECTOR_NOT || k == Kind::BITVECTOR_NEG)
  {
    terms.push_back(NodeManager::mkNode(k, t));
    return true;
  }
  // the remaining operators are binary, or n-ary and commutative, in which
  // case s is the operator applied to the remaining children
  if (nchildren < 2)
  {
    return false;
  }
  Node s;
  if (nchildren == 2)
  {
    s = svt[1 - index];
  }
  else
  {
    if (k != Kind::BITVECTOR_ADD && k != Kind::BITVECTOR_MULT
        && k != Kind::BITVECTOR_AND && k != Kind::BITVECTOR_OR
        && k != Kind::BITVECTOR_XOR)
    {
      return false;
    }
    std::vector<Node> schildren;
    for (size_t i = 0; i < nchildren; i++)
    {
      if (i != index)
      {
        schildren.push_back(svt[i]);
      }
    }
    s = nm->mkNode(k, schildren);
  }
  // whether x is the left operand, which matters for non-commutative operators
  bool xLeft = (index == 0);
  Node bvw = bv::utils::mkConst(nm, w, w);
  switch (k)
  {
    case Kind::BITVECTOR_ADD:
      terms.push_back(NodeManager::mkNode(Kind::BITVECTOR_SUB, t, s));
      break;
    case Kind::BITVECTOR_XOR:
      terms.push_back(NodeManager::mkNode(Kind::BITVECTOR_XOR, t, s));
      break;
    case Kind::BITVECTOR_MULT:
    {
      // (t udiv low(s)) * inv(s udiv low(s))
      Node low = mkLowBit(s);
      Node sodd = NodeManager::mkNode(Kind::BITVECTOR_UDIV, s, low);
      terms.push_back(
          NodeManager::mkNode(Kind::BITVECTOR_MULT,
                              NodeManager::mkNode(Kind::BITVECTOR_UDIV, t, low),
                              mkOddInverse(sodd)));
    }
    break;
    case Kind::BITVECTOR_UDIV:
      terms.push_back(xLeft ? NodeManager::mkNode(Kind::BITVECTOR_MULT, s, t)
                            : NodeManager::mkNode(Kind::BITVECTOR_UDIV, s, t));
      break;
    case Kind::BITVECTOR_UREM:
      terms.push_back(xLeft ? t
                            : NodeManager::mkNode(Kind::BITVECTOR_SUB, s, t));
      break;
    case Kind::BITVECTOR_AND:
    case Kind::BITVECTOR_OR: terms.push_back(t); break;
    case Kind::BITVECTOR_SHL:
      if (xLeft)
      {
        terms.push_back(NodeManager::mkNode(Kind::BITVECTOR_LSHR, t, s));
      }
      else
      {
        terms.push_back(NodeManager::mkNode(
            Kind::BITVECTOR_SUB, mkLog2(mkLowBit(t)), mkLog2(mkLowBit(s))));
        terms.push_back(bvw);
      }
      break;
    case Kind::BITVECTOR_LSHR:
      if (xLeft)
      {
        terms.push_back(NodeManager::mkNode(Kind::BITVECTOR_SHL, t, s));
      }
      else
      {
        terms.push_back(NodeManager::mkNode(
            Kind::BITVECTOR_SUB, mkLog2(mkHighBit(s)), mkLog2(mkHighBit(t))));
        terms.push_back(bvw);
      }
      break;
    case Kind::BITVECTOR_ASHR:
      if (xLeft)
      {
        terms.push_back(NodeManager::mkNode(Kind::BITVECTOR_SHL, t, s));
        terms.push_back(t);
      }
      else
      {
        // xor with the sign mask of s reduces to the logical shift case
        Node m = NodeManager::mkNode(
            Kind::BITVECTOR_ASHR, s, bv::utils::mkConst(nm, w, w - 1));
        Node sm = NodeManager::mkNode(Kind::BITVECTOR_XOR, s, m);
        Node tm = NodeManager::mkNode(Kind::BITVECTOR_XOR, t, m);
        terms.push_back(NodeManager::mkNode(
            Kind::BITVECTOR_SUB, mkLog2(mkHighBit(sm)), mkLog2(mkHighBit(tm))));
        terms.push_back(bvw);
      }
      break;
    default: return false;
  }
  return true;
}

Node BvElimSolver::solveBvLit(Node sv,
                              Node lit,
                              std::vector<uint32_t>& path,
                              Node svVal,
                              BvInverterQuery* m)
{
  Assert(!path.empty());
  // only positive equalities are handled
  if (lit.getKind() != Kind::EQUAL)
  {
    Trace("bv-elim") << "bv-elim : unhandled literal " << lit << std::endl;
    return Node::null();
  }
  uint32_t index = path.back();
  path.pop_back();
  Assert(index < 2);
  Node svt = lit[index];
  Node t = lit[1 - index];
  bool useModel = (m != nullptr && !svVal.isNull());
  while (!path.empty())
  {
    index = path.back();
    path.pop_back();
    std::vector<Node> terms;
    if (!getEqualityElimSet(svt, index, t, terms))
    {
      Trace("bv-elim") << "bv-elim : unhandled kind " << svt.getKind()
                       << " for " << svt << std::endl;
      return Node::null();
    }
    Assert(!terms.empty());
    // Choose a term from the elimination set. If we do not have a model, we
    // choose the first term.
    Node chosen;
    if (useModel)
    {
      // The value of the child we are solving for in the model. If a term in
      // the elimination set has this value, the remainder of the path is
      // solvable in the model.
      TNode tsv = sv;
      TNode tsvVal = svVal;
      Node cval = m->getModelValue(svt[index].substitute(tsv, tsvVal));
      Node firstSat;
      for (const Node& u : terms)
      {
        Node uval = m->getModelValue(u);
        if (uval == cval)
        {
          chosen = u;
          break;
        }
        if (firstSat.isNull())
        {
          // otherwise, remember the first term that satisfies the literal
          TNode tc = svt[index];
          TNode tu = u;
          Node ulit = svt.substitute(tc, tu);
          ulit = m->getModelValue(ulit.eqNode(t));
          if (ulit.isConst() && ulit.getConst<bool>())
          {
            firstSat = u;
          }
        }
      }
      if (chosen.isNull())
      {
        chosen = firstSat;
        Trace("bv-elim") << "bv-elim : no term matches the model value of "
                         << svt[index] << std::endl;
      }
    }
    if (chosen.isNull())
    {
      chosen = terms[0];
      Trace("bv-elim") << "bv-elim : no term is true in the model for " << svt
                       << " = " << t << ", choose " << chosen << std::endl;
    }
    Trace("bv-elim") << "bv-elim : solve " << svt << " = " << t << " for child "
                     << index << " by " << chosen << " from " << terms.size()
                     << " terms" << std::endl;
    t = chosen;
    svt = svt[index];
  }
  Assert(svt == sv);
  return t;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
