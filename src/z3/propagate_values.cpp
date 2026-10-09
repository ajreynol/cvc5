/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Propagating the values of unit assertions into the other assertions.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/solver/assertions/asserted_formulas.cpp, and recast in cvc5 style.
 */

#include "z3/propagate_values.h"

#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "z3/ast.h"

namespace cvc5::internal {
namespace z3 {

size_t PropagateValues::apply(std::vector<Node>& fmls)
{
  // asserted_formulas::propagate_values. Its loop repeats only while the
  // number of formulas grows, which rewriting in place never does, so it
  // amounts to one forward and one backward pass, each with a substitution
  // of its own.
  size_t prop = 0;
  d_subst.clear();
  for (size_t i = 0, sz = fmls.size(); i < sz; i++)
  {
    prop += propagate(fmls, i) ? 1 : 0;
  }
  d_subst.clear();
  for (size_t i = fmls.size(); i > 0; i--)
  {
    prop += propagate(fmls, i - 1) ? 1 : 0;
  }
  d_subst.clear();
  return prop;
}

bool PropagateValues::propagate(std::vector<Node>& fmls, size_t i)
{
  Node n = fmls[i];
  Node nn = n;
  if (!d_subst.empty())
  {
    std::unordered_map<TNode, Node> cache;
    nn = substitute(n, cache);
  }
  nn = d_rw.rewrite(nn);
  fmls[i] = nn;
  updateSubstitution(nn);
  return nn != n;
}

Node PropagateValues::substitute(TNode n, std::unordered_map<TNode, Node>& cache)
{
  auto it = d_subst.find(n);
  if (it != d_subst.end())
  {
    return it->second;
  }
  if (n.getNumChildren() == 0)
  {
    return n;
  }
  auto itc = cache.find(n);
  if (itc != cache.end())
  {
    return itc->second;
  }
  NodeManager* nm = n.getNodeManager();
  Node ret;
  if (n.isClosure())
  {
    // th_rewriter does not rewrite patterns (rewriter.rewrite_patterns
    // defaults to false), so only the body is substituted into.
    std::vector<Node> children{n[0], substitute(n[1], cache)};
    if (n.getNumChildren() == 3)
    {
      children.push_back(n[2]);
    }
    ret = children[1] == n[1] ? Node(n) : nm->mkNode(n.getKind(), children);
  }
  else
  {
    NodeBuilder nb(nm, n.getKind());
    if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      nb << n.getOperator();
    }
    bool changed = false;
    for (const Node& c : n)
    {
      Node cc = substitute(c, cache);
      changed = changed || cc != c;
      nb << cc;
    }
    ret = changed ? nb.constructNode() : Node(n);
  }
  cache[n] = ret;
  return ret;
}

void PropagateValues::updateSubstitution(TNode n)
{
  NodeManager* nm = n.getNodeManager();
  if (n.getKind() == Kind::EQUAL && !expr::hasBoundVar(n))
  {
    if (isGt(n[0], n[1]))
    {
      d_subst[n[0]] = n[1];
      return;
    }
    if (isGt(n[1], n[0]))
    {
      d_subst[n[1]] = n[0];
      return;
    }
  }
  if (n.getKind() == Kind::NOT)
  {
    d_subst[n[0]] = nm->mkConst(false);
  }
  else
  {
    d_subst[n] = nm->mkConst(true);
  }
}

bool PropagateValues::isGt(TNode lhs, TNode rhs)
{
  if (lhs == rhs)
  {
    return false;
  }
  // Values are always less in the ordering than non-values.
  bool v1 = lhs.isConst();
  bool v2 = rhs.isConst();
  if (!v1 && v2)
  {
    return true;
  }
  if (v1 && !v2)
  {
    return false;
  }
  uint32_t d1 = getDepth(lhs);
  uint32_t d2 = getDepth(rhs);
  if (d1 != d2)
  {
    return d1 > d2;
  }
  // Z3 compares the declarations' ids, which cvc5 has no equivalent of; the
  // ids of the nodes standing for them are the closest analogue. A constant
  // is a 0-ary application in Z3, and is its own declaration here.
  TNode f1 = getDecl(lhs);
  TNode f2 = getDecl(rhs);
  if (f1 != f2)
  {
    return f1.getId() > f2.getId();
  }
  if (lhs.getNumChildren() != rhs.getNumChildren())
  {
    return lhs.getNumChildren() > rhs.getNumChildren();
  }
  for (size_t i = 0, n = lhs.getNumChildren(); i < n; i++)
  {
    if (lhs[i] != rhs[i])
    {
      return isGt(lhs[i], rhs[i]);
    }
  }
  return false;
}

}  // namespace z3
}  // namespace cvc5::internal
