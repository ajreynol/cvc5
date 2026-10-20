/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The rewriting Z3 applies to its assertions around NNF.
 */

#include "preprocessing/z3/assertion_rewriter.h"

#include "expr/node_algorithm.h"
#include "expr/node_manager.h"
#include "smt/env.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace z3 {

Node AssertionRewriter::rewrite(TNode n)
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
    NodeManager* nm = n.getNodeManager();
    std::vector<Node> children{n[0], rewrite(n[1])};
    if (n.getNumChildren() == 3)
    {
      // The pattern list is carried over untouched: it is an annotation, not
      // a subformula, and rewriting a trigger would change what it matches.
      children.push_back(n[2]);
    }
    ret = nm->mkNode(n.getKind(), children);
  }
  else if (expr::hasClosure(Node(n)))
  {
    // A formula with a quantifier below it is rebuilt from rewritten
    // children, so that the rewriter never sees the quantifier itself.
    NodeManager* nm = n.getNodeManager();
    std::vector<Node> children;
    if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      children.push_back(n.getOperator());
    }
    bool changed = false;
    for (const Node& nc : n)
    {
      Node ncc = rewrite(nc);
      changed = changed || ncc != nc;
      children.push_back(ncc);
    }
    ret = changed ? nm->mkNode(n.getKind(), children) : Node(n);
  }
  else
  {
    ret = d_env.getRewriter()->rewrite(Node(n));
  }
  d_cache[n] = ret;
  return ret;
}

}  // namespace z3
}  // namespace cvc5::internal
