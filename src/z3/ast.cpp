/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The bridge between cvc5's Node and the term interface the ported Z3 core is
 * written against.
 */

#include "z3/ast.h"

#include "expr/node_algorithm.h"
#include "expr/node_manager.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "smt/env.h"
#include "theory/rewriter.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace z3 {

TNode getDecl(TNode n)
{
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    return n.getOperator();
  }
  if (NodeManager::hasOperator(n.getKind()))
  {
    return n.getNodeManager()->operatorOf(n.getKind());
  }
  // A leaf is its own declaration: it is congruent to nothing but itself.
  return n;
}

TheoryId familyIdOf(TNode n)
{
  return theory::Theory::theoryOf(
      n, options::TheoryOfMode::THEORY_OF_TYPE_BASED, theory::THEORY_UF);
}

bool isCommutative(TNode n)
{
  // Z3 consults func_decl::is_commutative(), which the congruence table uses
  // to normalize the argument order of binary applications. Only the binary
  // case matters, since that is the only specialization of the table that
  // treats arguments as unordered.
  if (n.getNumChildren() != 2)
  {
    return false;
  }
  switch (n.getKind())
  {
    case Kind::EQUAL:
    case Kind::AND:
    case Kind::OR:
    case Kind::XOR:
    case Kind::ADD:
    case Kind::MULT:
    case Kind::NONLINEAR_MULT:
    case Kind::BITVECTOR_ADD:
    case Kind::BITVECTOR_MULT:
    case Kind::BITVECTOR_AND:
    case Kind::BITVECTOR_OR:
    case Kind::BITVECTOR_XOR:
    case Kind::BITVECTOR_XNOR:
    case Kind::BITVECTOR_NAND:
    case Kind::BITVECTOR_NOR:
    case Kind::BITVECTOR_COMP: return true;
    default: return false;
  }
}

bool hasPatterns(TNode q)
{
  Assert(isQuantifier(q));
  if (q.getNumChildren() < 3)
  {
    return false;
  }
  for (const Node& p : q[2])
  {
    if (p.getKind() == Kind::INST_PATTERN)
    {
      return true;
    }
  }
  return false;
}

void getPatterns(TNode q, std::vector<std::vector<Node>>& patterns)
{
  Assert(isQuantifier(q));
  if (q.getNumChildren() < 3)
  {
    return;
  }
  for (const Node& p : q[2])
  {
    if (p.getKind() == Kind::INST_PATTERN)
    {
      patterns.emplace_back(p.begin(), p.end());
    }
  }
}

void getNoPatterns(TNode q, std::vector<Node>& noPatterns)
{
  Assert(isQuantifier(q));
  if (q.getNumChildren() < 3)
  {
    return;
  }
  for (const Node& p : q[2])
  {
    if (p.getKind() == Kind::INST_NO_PATTERN)
    {
      noPatterns.insert(noPatterns.end(), p.begin(), p.end());
    }
  }
}

uint32_t getWeight(TNode q)
{
  Assert(isQuantifier(q));
  // cvc5's parser does not retain ":weight", so the only weights seen here
  // are the ones pattern inference assigns. The default is Z3's, which is 1
  // and not 0: with weight 0 the cost of an instance is its generation, the
  // generation of the enodes an instance creates is its cost, and so every
  // instance has cost 0 and matching loops are never broken. See the long
  // comment on the "weight 0" performance bug in Z3's qi_params.h.
  uint64_t cached = q.getAttribute(QuantWeightAttr());
  return cached == 0 ? s_defaultWeight : static_cast<uint32_t>(cached - 1);
}

void setWeight(TNode q, uint32_t w)
{
  Assert(isQuantifier(q));
  q.setAttribute(QuantWeightAttr(), static_cast<uint64_t>(w) + 1);
}

std::string getQid(TNode q)
{
  Assert(isQuantifier(q));
  if (q.getNumChildren() < 3)
  {
    return "";
  }
  for (const Node& p : q[2])
  {
    if (p.getKind() == Kind::INST_ATTRIBUTE && p.getNumChildren() > 0
        && p[0].getAttribute(theory::QuantNameAttribute()))
    {
      return p[0].getName();
    }
  }
  return "";
}

uint32_t getDepth(TNode n)
{
  uint64_t cached = n.getAttribute(TermDepthAttr());
  if (cached != 0)
  {
    return static_cast<uint32_t>(cached);
  }
  // An explicit stack, since the terms this is asked about may be deep enough
  // to overflow the call stack -- which is the reason it is asked at all.
  std::vector<TNode> visit{n};
  while (!visit.empty())
  {
    TNode cur = visit.back();
    if (cur.getAttribute(TermDepthAttr()) != 0)
    {
      visit.pop_back();
      continue;
    }
    uint64_t maxChild = 0;
    bool incomplete = false;
    for (const Node& c : cur)
    {
      uint64_t d = c.getAttribute(TermDepthAttr());
      if (d == 0)
      {
        visit.push_back(c);
        incomplete = true;
      }
      else if (d > maxChild)
      {
        maxChild = d;
      }
    }
    if (incomplete)
    {
      continue;
    }
    visit.pop_back();
    cur.setAttribute(TermDepthAttr(), maxChild + 1);
  }
  return static_cast<uint32_t>(n.getAttribute(TermDepthAttr()));
}

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
    ret = d_nm->mkNode(Kind::OR,
                       children[0].notNode(),
                       children[1]);
  }
  else if (k == Kind::XOR)
  {
    Assert(children.size() == 2);
    ret = d_nm->mkNode(Kind::EQUAL, children[0], children[1]).notNode();
  }
  else if (k == Kind::AND && d_eliminateAnd)
  {
    // Z3's core never sees a conjunction: asserted_formulas::reduce() calls
    // set_eliminate_and(true) once NNF is done, and the rewrite pass that
    // follows turns every (and a b) into (not (or (not a) (not b))).
    //
    // This is off by default even so, which is the one place in this port
    // where a faithful reproduction of Z3 measured worse. On the formula
    // examined most closely it does what it should -- decisions went from
    // 3469 to 2856 against Z3's 2590, Boolean variables from 7406 to 7076 --
    // but over the 300-benchmark sample it cost nine solved benchmarks.
    // Something downstream is tuned, deliberately or not, to the conjunctions
    // being there; until that is found, the measurement wins.
    std::vector<Node> negated;
    for (const Node& c : children)
    {
      negated.push_back(c.notNode());
    }
    ret = d_nm->mkNode(Kind::OR, negated).notNode();
  }
  else
  {
    ret = changed ? d_nm->mkNode(k, children) : Node(n);
  }
  d_cache[n] = ret;
  return ret;
}

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

QuantifierNormalizer::QuantifierNormalizer(NodeManager* nm) : d_nm(nm) {}

Node QuantifierNormalizer::mkVar(uint32_t idx, const TypeNode& tn)
{
  if (idx >= d_vars.size())
  {
    d_vars.resize(idx + 1);
  }
  std::unordered_map<TypeNode, Node>& m = d_vars[idx];
  auto it = m.find(tn);
  if (it != m.end())
  {
    return it->second;
  }
  std::stringstream ss;
  ss << "z3v" << idx;
  Node v = NodeManager::mkBoundVar(ss.str(), tn);
  v.setAttribute(QuantVarLevelAttr(), static_cast<uint64_t>(idx) + 1);
  m[tn] = v;
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
