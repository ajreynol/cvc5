/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The elimination of the connectives the ported core does not internalize.
 */

#include "preprocessing/z3/connective_normalizer.h"

#include "expr/node_manager.h"

namespace cvc5::internal {
namespace z3 {

Node ConnectiveNormalizer::normalize(TNode n)
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
  std::vector<Node> children;
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    children.push_back(n.getOperator());
  }
  bool changed = false;
  for (const Node& nc : n)
  {
    Node ncc = normalize(nc);
    changed = changed || ncc != nc;
    children.push_back(ncc);
  }
  Node ret;
  Kind k = n.getKind();
  if (k == Kind::IMPLIES)
  {
    Assert(children.size() == 2);
    ret = d_nm->mkNode(Kind::OR, children[0].notNode(), children[1]);
  }
  else if (k == Kind::XOR)
  {
    Assert(children.size() == 2);
    ret = d_nm->mkNode(Kind::EQUAL, children[0], children[1]).notNode();
  }
  else
  {
    ret = changed ? d_nm->mkNode(k, children) : Node(n);
  }
  d_cache[n] = ret;
  return ret;
}

}  // namespace z3
}  // namespace cvc5::internal
