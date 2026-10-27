/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The quantified variables of the ported Z3 core.
 */

#include "z3/quantifiers/quantifier_normalizer.h"

#include "expr/bound_var_manager.h"
#include "expr/node_algorithm.h"
#include "expr/node_manager.h"

namespace cvc5::internal {
namespace z3 {

QuantifierNormalizer::QuantifierNormalizer(NodeManager* nm) : d_nm(nm) {}

Node QuantifierNormalizer::mkVar(uint32_t idx, const TypeNode& tn)
{
  std::stringstream ss;
  ss << "z3v" << idx;
  Node v = d_nm->getBoundVarManager()->mkBoundVar(
      BoundVarId::Z3_QUANT_VAR,
      BoundVarManager::getCacheValue(d_nm, idx),
      ss.str(),
      tn);
  v.setAttribute(QuantVarLevelAttr(), static_cast<uint64_t>(idx) + 1);
  return v;
}

Node QuantifierNormalizer::normalize(TNode n)
{
  auto it = d_cache.find(n);
  if (it != d_cache.end())
  {
    return it->second;
  }
  std::unordered_map<Node, Node> subs;
  Node ret = normalizeRec(n, 0, subs);
  d_cache[n] = ret;
  return ret;
}

Node QuantifierNormalizer::normalizeRec(TNode n,
                                        uint32_t depth,
                                        std::unordered_map<Node, Node>& subs)
{
  if (n.getKind() == Kind::BOUND_VARIABLE)
  {
    auto it = subs.find(n);
    return it != subs.end() ? it->second : Node(n);
  }
  // Ground subterms are already canonical. This is the common case by far and
  // keeps normalization proportional to the quantified part of the input.
  if (!expr::hasBoundVar(n))
  {
    return n;
  }
  if (isQuantifier(n))
  {
    TNode bvl = n[0];
    size_t numDecls = bvl.getNumChildren();
    // Save any bindings we are about to shadow, so that an inner binder
    // reusing a variable node of an outer one behaves correctly.
    std::vector<std::pair<Node, Node>> shadowed;
    std::vector<Node> newVars;
    for (size_t i = 0; i < numDecls; i++)
    {
      Node v = bvl[i];
      auto it = subs.find(v);
      if (it != subs.end())
      {
        shadowed.emplace_back(v, it->second);
      }
      Node cv = mkVar(static_cast<uint32_t>(depth + i), v.getType());
      newVars.push_back(cv);
      subs[v] = cv;
    }
    uint32_t newDepth = depth + static_cast<uint32_t>(numDecls);
    std::vector<Node> children;
    children.push_back(d_nm->mkNode(Kind::BOUND_VAR_LIST, newVars));
    children.push_back(normalizeRec(n[1], newDepth, subs));
    if (n.getNumChildren() == 3)
    {
      children.push_back(normalizePatternList(n[2], newDepth, subs));
    }
    // Restore the substitution.
    for (size_t i = 0; i < numDecls; i++)
    {
      subs.erase(bvl[i]);
    }
    for (const std::pair<Node, Node>& p : shadowed)
    {
      subs[p.first] = p.second;
    }
    return d_nm->mkNode(n.getKind(), children);
  }
  std::vector<Node> children;
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    children.push_back(n.getOperator());
  }
  for (const Node& nc : n)
  {
    children.push_back(normalizeRec(nc, depth, subs));
  }
  return d_nm->mkNode(n.getKind(), children);
}

Node QuantifierNormalizer::normalizePatternList(
    TNode ipl, uint32_t depth, std::unordered_map<Node, Node>& subs)
{
  Assert(ipl.getKind() == Kind::INST_PATTERN_LIST);
  std::vector<Node> annotations;
  for (const Node& p : ipl)
  {
    Kind pk = p.getKind();
    if (pk == Kind::INST_PATTERN || pk == Kind::INST_NO_PATTERN
        || pk == Kind::INST_POOL || pk == Kind::INST_ADD_TO_POOL)
    {
      std::vector<Node> terms;
      for (const Node& t : p)
      {
        terms.push_back(normalizeRec(t, depth, subs));
      }
      annotations.push_back(d_nm->mkNode(pk, terms));
    }
    else
    {
      // Attributes such as ":qid" do not mention the bound variables.
      annotations.push_back(p);
    }
  }
  return d_nm->mkNode(Kind::INST_PATTERN_LIST, annotations);
}

}  // namespace z3
}  // namespace cvc5::internal
