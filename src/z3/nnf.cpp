/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Negation normal form with skolemization.
 */

#include "z3/nnf.h"

#include "expr/node_algorithm.h"
#include "expr/node_manager.h"
#include "expr/skolem_manager.h"
#include "z3/ast.h"

namespace cvc5::internal {
namespace z3 {

Node Nnf::convert(TNode n)
{
  if (!expr::hasClosure(Node(n)))
  {
    return n;
  }
  std::vector<Node> scope;
  return convertRec(n, true, scope);
}

Node Nnf::mkSkolem(TNode v, const std::vector<Node>& scope)
{
  SkolemManager* sm = d_nm->getSkolemManager();
  if (scope.empty())
  {
    return sm->mkDummySkolem("z3sk", v.getType());
  }
  std::vector<TypeNode> argTypes;
  for (const Node& s : scope)
  {
    argTypes.push_back(s.getType());
  }
  TypeNode ft = d_nm->mkFunctionType(argTypes, v.getType());
  Node f = sm->mkDummySkolem("z3sk", ft);
  std::vector<Node> children{f};
  children.insert(children.end(), scope.begin(), scope.end());
  return d_nm->mkNode(Kind::APPLY_UF, children);
}

Node Nnf::convertRec(TNode n, bool pol, const std::vector<Node>& scope)
{
  Assert(n.getType().isBoolean());
  if (!expr::hasClosure(Node(n)))
  {
    // No quantifier below this point, so there is nothing to normalize; the
    // shape cvc5's preprocessor produced is kept as it is.
    std::unordered_map<Node, Node>& cache = d_cache[pol ? 1 : 0];
    auto it = cache.find(n);
    if (it != cache.end())
    {
      return it->second;
    }
    Node ret = pol ? Node(n) : n.negate();
    cache[n] = ret;
    return ret;
  }
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::NOT: return convertRec(n[0], !pol, scope);
    case Kind::AND:
    case Kind::OR:
    {
      std::vector<Node> children;
      for (const Node& nc : n)
      {
        children.push_back(convertRec(nc, pol, scope));
      }
      Kind rk = (k == Kind::AND) == pol ? Kind::AND : Kind::OR;
      return d_nm->mkNode(rk, children);
    }
    case Kind::IMPLIES:
    {
      // (=> a b) is (or (not a) b)
      Node a = convertRec(n[0], !pol, scope);
      Node b = convertRec(n[1], pol, scope);
      return d_nm->mkNode(pol ? Kind::OR : Kind::AND, a, b);
    }
    case Kind::XOR:
    {
      // (xor a b) is (not (= a b))
      Node eq = d_nm->mkNode(Kind::EQUAL, n[0], n[1]);
      return convertRec(eq, !pol, scope);
    }
    case Kind::EQUAL:
    {
      if (!n[0].getType().isBoolean())
      {
        break;
      }
      // A quantifier under an equivalence occurs with both polarities, so the
      // equivalence is expanded; this is what Z3's nnf does as well.
      Node ap = convertRec(n[0], true, scope);
      Node an = convertRec(n[0], false, scope);
      Node bp = convertRec(n[1], true, scope);
      Node bn = convertRec(n[1], false, scope);
      if (pol)
      {
        return d_nm->mkNode(Kind::AND,
                            d_nm->mkNode(Kind::OR, an, bp),
                            d_nm->mkNode(Kind::OR, ap, bn));
      }
      return d_nm->mkNode(Kind::AND,
                          d_nm->mkNode(Kind::OR, ap, bp),
                          d_nm->mkNode(Kind::OR, an, bn));
    }
    case Kind::ITE:
    {
      if (!n.getType().isBoolean())
      {
        break;
      }
      Node cp = convertRec(n[0], true, scope);
      Node cn = convertRec(n[0], false, scope);
      Node t = convertRec(n[1], pol, scope);
      Node e = convertRec(n[2], pol, scope);
      return d_nm->mkNode(pol ? Kind::AND : Kind::OR,
                          d_nm->mkNode(pol ? Kind::OR : Kind::AND, cn, t),
                          d_nm->mkNode(pol ? Kind::OR : Kind::AND, cp, e));
    }
    case Kind::FORALL:
    case Kind::EXISTS:
    {
      bool universal = (k == Kind::FORALL) == pol;
      if (universal)
      {
        std::vector<Node> newScope = scope;
        for (const Node& v : n[0])
        {
          newScope.push_back(v);
        }
        Node body = convertRec(n[1], pol, newScope);
        std::vector<Node> children{n[0], body};
        if (n.getNumChildren() == 3)
        {
          children.push_back(n[2]);
        }
        return d_nm->mkNode(Kind::FORALL, children);
      }
      // An existential: skolemize it, which is what makes every surviving
      // quantifier universal.
      std::vector<Node> vars;
      std::vector<Node> subs;
      for (const Node& v : n[0])
      {
        vars.push_back(v);
        subs.push_back(mkSkolem(v, scope));
      }
      Node body =
          n[1].substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
      return convertRec(body, pol, scope);
    }
    default: break;
  }
  // A quantifier below an operator the normal form does not descend into,
  // such as a term if-then-else or an uninterpreted predicate. Leaving it
  // alone would break the positive-polarity invariant, so the caller is
  // responsible for noticing; in practice cvc5's preprocessor does not
  // produce such a formula.
  return pol ? Node(n) : n.negate();
}

}  // namespace z3
}  // namespace cvc5::internal
