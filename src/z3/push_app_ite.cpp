/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Lifting if-then-else out of non-ground applications.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/ast/rewriter/push_app_ite.cpp, and recast in cvc5 style.
 */

#include "z3/push_app_ite.h"

#include "expr/node_algorithm.h"
#include "expr/node_builder.h"

namespace cvc5::internal {
namespace z3 {

Node NgPushAppIte::apply(TNode n) { return applyRec(n); }

Node NgPushAppIte::applyRec(TNode n)
{
  if (n.getNumChildren() == 0)
  {
    return n;
  }
  auto it = d_cache.find(n);
  if (it != d_cache.end())
  {
    return it->second;
  }
  Node ret;
  if (n.isClosure())
  {
    // rewrite_patterns() is false in push_app_ite_cfg, so the pattern list is
    // carried over untouched and only the body is rewritten.
    std::vector<Node> children{n[0], applyRec(n[1])};
    if (n.getNumChildren() == 3)
    {
      children.push_back(n[2]);
    }
    ret = d_nm->mkNode(n.getKind(), children);
  }
  else
  {
    NodeBuilder nb(d_nm, n.getKind());
    if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      nb << n.getOperator();
    }
    for (const Node& nc : n)
    {
      nb << applyRec(nc);
    }
    ret = reduceApp(nb.constructNode());
  }
  d_cache[n] = ret;
  return ret;
}

Node NgPushAppIte::reduceApp(TNode n)
{
  if (!isTarget(n))
  {
    return n;
  }
  // has_ite_arg: the first if-then-else argument, of any sort. is_target only
  // counted the non-Boolean ones, so with a Boolean if-then-else before the
  // non-Boolean one this lifts the Boolean one; Z3 does the same.
  size_t idx = 0;
  while (n[idx].getKind() != Kind::ITE)
  {
    idx++;
  }
  TNode ite = n[idx];
  Node branch[2];
  for (size_t b = 0; b < 2; b++)
  {
    NodeBuilder nb(d_nm, n.getKind());
    if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      nb << n.getOperator();
    }
    for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; i++)
    {
      nb << (i == idx ? ite[b + 1] : n[i]);
    }
    // BR_REWRITE2: the two new applications are reduced again, their
    // arguments are not.
    branch[b] = reduceApp(nb.constructNode());
  }
  return d_nm->mkNode(Kind::ITE, ite[0], branch[0], branch[1]);
}

bool NgPushAppIte::isTarget(TNode n) const
{
  // push_app_ite_cfg::is_target
  if (n.getKind() == Kind::ITE || n.isClosure())
  {
    return false;
  }
  bool foundIte = false;
  for (const Node& nc : n)
  {
    if (nc.getKind() == Kind::ITE && !nc.getType().isBoolean())
    {
      if (foundIte)
      {
        if (d_conservative)
        {
          return false;
        }
      }
      else
      {
        foundIte = true;
      }
    }
  }
  if (!foundIte)
  {
    return false;
  }
  // ng_push_app_ite_cfg::is_target: some argument is not ground.
  for (const Node& nc : n)
  {
    if (expr::hasBoundVar(nc))
    {
      return true;
    }
  }
  return false;
}

}  // namespace z3
}  // namespace cvc5::internal
