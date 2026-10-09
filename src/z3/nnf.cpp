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

#include <algorithm>
#include <unordered_set>

#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "expr/skolem_manager.h"
#include "z3/ast.h"

namespace cvc5::internal {
namespace z3 {

Node Nnf::convert(TNode n)
{
  std::vector<Node> scope;
  Node r = convertRec(n, true, scope);
  // nnf::operator(): the definitions introduced while converting are
  // converted in turn, which may introduce more, and are then reversed.
  size_t first = d_defs.size();
  for (size_t i = 0; i < d_todoDefs.size(); i++)
  {
    Node def = d_todoDefs[i];
    d_defs.push_back(convertRec(def, true, scope));
  }
  d_todoDefs.clear();
  std::reverse(d_defs.begin() + first, d_defs.end());
  return r;
}

std::vector<Node> Nnf::takeDefinitions()
{
  std::vector<Node> defs;
  defs.swap(d_defs);
  return defs;
}

Node Nnf::nameQuantifiers(TNode n, const std::vector<Node>& scope)
{
  // name_exprs_core is a rewriter whose get_subst replaces a subterm the
  // predicate accepts, without descending into it; the predicate of the
  // quantifier label namer accepts quantifiers.
  if (n.getKind() == Kind::FORALL || n.getKind() == Kind::EXISTS)
  {
    return mkName(n, scope);
  }
  if (n.isClosure() || !expr::hasClosure(Node(n)))
  {
    return n;
  }
  NodeBuilder nb(d_nm, n.getKind());
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    nb << n.getOperator();
  }
  for (const Node& nc : n)
  {
    nb << nameQuantifiers(nc, scope);
  }
  return nb.constructNode();
}

Node Nnf::mkName(TNode q, const std::vector<Node>& scope)
{
  auto it = d_names.find(q);
  if (it != d_names.end())
  {
    return it->second;
  }
  // gen_name: the name is applied to the variables of q's free de Bruijn
  // indices, index 0 first; an index q does not use is filled with true. A
  // variable of scope at position j has de Bruijn index scope.size()-1-j.
  std::unordered_set<Node> fvs;
  expr::getFreeVariables(q, fvs);
  // used_vars visits the patterns as well as the body, and a Verus pattern
  // may mention an enclosing variable the body does not use.
  if (q.getNumChildren() == 3)
  {
    std::unordered_set<Node> pfvs;
    expr::getFreeVariables(q[2], pfvs);
    for (const Node& v : q[0])
    {
      pfvs.erase(v);
    }
    fvs.insert(pfvs.begin(), pfvs.end());
  }
  size_t numVars = 0;
  for (size_t j = 0, ns = scope.size(); j < ns; j++)
  {
    if (fvs.find(scope[j]) != fvs.end())
    {
      numVars = std::max(numVars, ns - j);
    }
  }
  std::vector<Node> args;
  std::vector<TypeNode> argTypes;
  for (size_t i = 0; i < numVars; i++)
  {
    TNode v = scope[scope.size() - 1 - i];
    if (fvs.find(v) != fvs.end())
    {
      args.push_back(v);
      argTypes.push_back(v.getType());
    }
    else
    {
      args.push_back(d_nm->mkConst(true));
      argTypes.push_back(d_nm->booleanType());
    }
  }
  SkolemManager* sm = d_nm->getSkolemManager();
  Node name;
  if (args.empty())
  {
    name = sm->mkDummySkolem("z3name", d_nm->booleanType());
  }
  else
  {
    TypeNode ft = d_nm->mkFunctionType(argTypes, d_nm->booleanType());
    std::vector<Node> children{sm->mkDummySkolem("z3name", ft)};
    children.insert(children.end(), args.begin(), args.end());
    name = d_nm->mkNode(Kind::APPLY_UF, children);
  }
  d_names[q] = name;
  // mk_definition for a Boolean expression: (or (not n) q) and (or n (not
  // q)), each closed over the variables it uses with n as its only pattern
  // and no qid (bound_vars, then elim_unused_vars). The bound variables are
  // listed outermost first, as the reversed var_sorts are.
  std::vector<Node> bvs;
  for (const Node& v : scope)
  {
    if (fvs.find(v) != fvs.end())
    {
      bvs.push_back(v);
    }
  }
  Node conj[2] = {d_nm->mkNode(Kind::OR, name.negate(), q),
                  d_nm->mkNode(Kind::OR, name, q.negate())};
  if (!bvs.empty())
  {
    Node bvl = d_nm->mkNode(Kind::BOUND_VAR_LIST, bvs);
    Node pat = d_nm->mkNode(Kind::INST_PATTERN_LIST,
                            d_nm->mkNode(Kind::INST_PATTERN, name));
    for (Node& c : conj)
    {
      c = d_nm->mkNode(Kind::FORALL, bvl, c, pat);
    }
  }
  d_todoDefs.push_back(d_nm->mkNode(Kind::AND, conj[0], conj[1]));
  return name;
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
  // An atom with a quantifier below it, e.g. (= (f x) (B (forall y P))):
  // process_default. The quantifier cannot reach the core in either polarity
  // from inside a term, so it is replaced by a fresh name whose definition
  // is asserted separately; converting the definition is what skolemizes
  // the quantifier's negative half. Verus emits these for every lambda whose
  // body is a quantified formula.
  Node named = nameQuantifiers(n, scope);
  return pol ? named : named.negate();
}

}  // namespace z3
}  // namespace cvc5::internal
