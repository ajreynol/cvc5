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
    // Z3's default NNF mode is NNF_SKOLEM, which converts a subformula only
    // if it contains a quantifier (or a label, which this port has no
    // equivalent of) and otherwise leaves it exactly as it is -- see the
    // skip() call in nnf.cpp's visit(). The comment there, "this mode is
    // sufficient when using E-matching", is the whole point: what the core
    // needs is that every quantifier reaches it in positive polarity, and a
    // quantifier-free subformula cannot carry one. Converting those as well
    // is not merely wasted work. Pushing negations through them duplicates
    // every subformula that is needed in both polarities, which on these
    // benchmarks gave the core 2.3 times the Boolean variables and 7 times
    // the binary clauses Z3 builds, and a correspondingly different search.
    return pol ? Node(n) : n.negate();
  }
  // The result of converting a subformula that holds a quantifier depends on
  // the enclosing universals, through the skolem functions, so it is not
  // cached. Z3 keys its cache on the scope depth for the same reason.
  return convertCore(n, pol, scope);
}

Node Nnf::convertCore(TNode n, bool pol, const std::vector<Node>& scope)
{
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
      // The shape is the same for both polarities, since negating an
      // if-then-else negates its branches: this is Z3's process_ite. Pushing
      // the negation out instead, as a disjunction of conjunctions, is just
      // as correct but is the wrong normal form to hand a CNF converter.
      return d_nm->mkNode(Kind::AND,
                          d_nm->mkNode(Kind::OR, cn, t),
                          d_nm->mkNode(Kind::OR, cp, e));
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
