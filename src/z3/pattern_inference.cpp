/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Pattern inference for quantifiers without a :pattern annotation.
 *
 * Ported from Z3's src/ast/pattern/pattern_inference.cpp
 * (Copyright (c) 2006 Microsoft Corporation, MIT license, author Leonardo de
 * Moura) and recast in cvc5's style.
 */

#include "z3/pattern_inference.h"

#include <algorithm>
#include <sstream>

#include "base/output.h"
#include "expr/node_algorithm.h"
#include "expr/node_manager.h"
#include "z3/ast.h"
#include "z3/params.h"

namespace cvc5::internal {
namespace z3 {

namespace {

/**
 * The kinds of Z3's basic family, which may not be at the root of a pattern.
 * Z3 permits true and false, but those are ground and therefore never
 * candidates anyway.
 */
bool isCoreKind(Kind k)
{
  switch (k)
  {
    case Kind::NOT:
    case Kind::AND:
    case Kind::OR:
    case Kind::IMPLIES:
    case Kind::XOR:
    case Kind::ITE:
    case Kind::EQUAL:
    case Kind::DISTINCT: return true;
    default: return false;
  }
}

/** The kinds of Z3's arithmetic family. */
bool isArithKind(Kind k)
{
  switch (k)
  {
    case Kind::ADD:
    case Kind::SUB:
    case Kind::NEG:
    case Kind::MULT:
    case Kind::NONLINEAR_MULT:
    case Kind::IAND:
    case Kind::POW2:
    case Kind::DIVISION:
    case Kind::DIVISION_TOTAL:
    case Kind::INTS_DIVISION:
    case Kind::INTS_DIVISION_TOTAL:
    case Kind::INTS_MODULUS:
    case Kind::INTS_MODULUS_TOTAL:
    case Kind::ABS:
    case Kind::DIVISIBLE:
    case Kind::POW:
    case Kind::EXPONENTIAL:
    case Kind::SINE:
    case Kind::COSINE:
    case Kind::TANGENT:
    case Kind::TO_REAL:
    case Kind::TO_INTEGER:
    case Kind::IS_INTEGER:
    case Kind::LT:
    case Kind::LEQ:
    case Kind::GT:
    case Kind::GEQ: return true;
    default: return false;
  }
}

/**
 * The arithmetic operators Z3 is willing to put directly at the root of a
 * pattern once nested-only inference has failed, i.e. OP_DIV, OP_IDIV,
 * OP_MOD, OP_REM and OP_MUL.
 */
bool isMulDivModKind(Kind k)
{
  switch (k)
  {
    case Kind::MULT:
    case Kind::NONLINEAR_MULT:
    case Kind::DIVISION:
    case Kind::DIVISION_TOTAL:
    case Kind::INTS_DIVISION:
    case Kind::INTS_DIVISION_TOTAL:
    case Kind::INTS_MODULUS:
    case Kind::INTS_MODULUS_TOTAL: return true;
    default: return false;
  }
}

/** True if the symbol at the root of n was introduced by skolemization. */
bool isSkolemApp(TNode n)
{
  return n.getKind() == Kind::APPLY_UF
         && n.getOperator().getKind() == Kind::SKOLEM;
}

}  // namespace

// ------------------------------------------------------- smaller pattern

void SmallerPattern::save(TNode p1, TNode p2)
{
  ExprPair e(p1, p2);
  if (d_cache.find(e) == d_cache.end())
  {
    d_cache.insert(e);
    d_todo.push_back(e);
  }
}

bool SmallerPattern::process(TNode p1, TNode p2)
{
  d_todo.clear();
  d_cache.clear();
  save(p1, p2);
  while (!d_todo.empty())
  {
    ExprPair curr = d_todo.back();
    d_todo.pop_back();
    TNode n1 = curr.first;
    TNode n2 = curr.second;
    if (isVar(n1))
    {
      uint32_t idx = varIndex(n1);
      if (idx >= d_base && idx - d_base < d_bindings.size())
      {
        Node& b = d_bindings[idx - d_base];
        if (b.isNull())
        {
          b = n2;
        }
        else if (b != n2)
        {
          return false;
        }
      }
      else if (n1 != n2)
      {
        // a variable bound by an external quantifier
        return false;
      }
      continue;
    }
    if (isVar(n2) || isQuantifier(n1) != isQuantifier(n2))
    {
      return false;
    }
    if (isQuantifier(n1))
    {
      if (n1 != n2)
      {
        return false;
      }
      continue;
    }
    if (n1.getNumChildren() != n2.getNumChildren()
        || getDecl(n1) != getDecl(n2))
    {
      return false;
    }
    if (n1.getNumChildren() == 0)
    {
      if (n1 != n2)
      {
        return false;
      }
      continue;
    }
    for (size_t i = 0, sz = n1.getNumChildren(); i < sz; ++i)
    {
      save(n1[i], n2[i]);
    }
  }
  return true;
}

bool SmallerPattern::operator()(size_t base,
                                size_t numBindings,
                                TNode p1,
                                TNode p2)
{
  d_base = base;
  d_bindings.assign(numBindings, Node::null());
  return process(p1, p2);
}

// ---------------------------------------------------- pattern inference

PatternInference::PatternInference(NodeManager* nm, const Params& params)
    : d_nm(nm),
      d_params(params),
      d_forbidArith(params.d_piArith == Params::AP_NO),
      d_baseLevel(0),
      d_numBindings(0),
      d_noPatterns(nullptr),
      d_nestedArithOnly(true),
      d_blockLoopPatterns(params.d_piBlockLoopPatterns),
      d_decomposePatterns(params.d_piDecomposePatterns),
      d_patternWeightLt(d_candidatesInfo)
{
}

PatternInference::~PatternInference() {}

Node PatternInference::apply(TNode n)
{
  if (!d_params.d_piEnabled || !expr::hasClosure(Node(n)))
  {
    return n;
  }
  return applyRec(n);
}

Node PatternInference::applyRec(TNode n)
{
  auto it = d_cache.find(n);
  if (it != d_cache.end())
  {
    return it->second;
  }
  Node ret;
  if (!expr::hasClosure(Node(n)))
  {
    // No quantifier below this point, so there is nothing to infer.
    ret = n;
  }
  else if (n.getKind() == Kind::FORALL || n.getKind() == Kind::EXISTS)
  {
    Node newBody = applyRec(n[1]);
    ret = reduceQuantifier(n, newBody);
  }
  else
  {
    std::vector<Node> children;
    if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      children.push_back(n.getOperator());
    }
    bool changed = false;
    for (const Node& nc : n)
    {
      Node ncc = applyRec(nc);
      changed = changed || ncc != nc;
      children.push_back(ncc);
    }
    ret = changed ? d_nm->mkNode(n.getKind(), children) : Node(n);
  }
  d_cache[n] = ret;
  return ret;
}

// ------------------------------------------------- candidate collection

void PatternInference::collect(TNode n)
{
  Assert(d_collectTodo.empty());
  d_collectTodo.push_back(n);
  while (!d_collectTodo.empty())
  {
    TNode curr = d_collectTodo.back();
    if (collectVisitChildren(curr))
    {
      d_collectTodo.pop_back();
      collectSaveCandidate(curr);
    }
  }
  d_collectCache.clear();
}

bool PatternInference::collectVisitChildren(TNode n)
{
  bool visited = true;
  if (isQuantifier(n))
  {
    if (d_collectCache.find(n[1]) == d_collectCache.end())
    {
      d_collectTodo.push_back(n[1]);
      visited = false;
    }
    return visited;
  }
  size_t i = n.getNumChildren();
  while (i > 0)
  {
    --i;
    if (d_collectCache.find(n[i]) == d_collectCache.end())
    {
      d_collectTodo.push_back(n[i]);
      visited = false;
    }
  }
  return visited;
}

void PatternInference::collectSave(TNode n, CollectInfo* i)
{
  d_collectCache[n] = std::unique_ptr<CollectInfo>(i);
}

void PatternInference::collectSaveCandidate(TNode n)
{
  if (isVar(n))
  {
    UIntSet freeVars;
    UIntSet boundVars;
    uint32_t idx = varIndex(n);
    // The levels are absolute, so no shifting is needed: the variables of the
    // quantifier being processed are the ones in
    // [d_baseLevel, d_baseLevel + d_numBindings), the deeper levels belong to
    // a nested quantifier, and a shallower level belongs to an enclosing
    // quantifier -- which Z3 counts as neither free nor bound, since such a
    // variable is fixed from the point of view of this quantifier.
    if (idx >= d_baseLevel && idx < d_baseLevel + d_numBindings)
    {
      freeVars.insert(idx - d_baseLevel);
    }
    else if (idx >= d_baseLevel + d_numBindings)
    {
      boundVars.insert(idx);
    }
    collectSave(n, new CollectInfo(freeVars, boundVars, 1));
    return;
  }

  if (isQuantifier(n))
  {
    auto it = d_collectCache.find(n[1]);
    Assert(it != d_collectCache.end());
    CollectInfo* bodyInfo = it->second.get();
    if (bodyInfo == nullptr)
    {
      collectSave(n, nullptr);
      return;
    }
    // The nested quantifier's own variables are no longer bound once we leave
    // it, while the ones of a quantifier nested deeper still are. Since the
    // levels are absolute nothing is renumbered: only n's own levels are
    // dropped.
    UIntSet boundVars = bodyInfo->d_boundVars;
    size_t numDecls = getNumDecls(n);
    size_t base = varIndex(n[0][0]);
    for (size_t i = 0; i < numDecls; ++i)
    {
      boundVars.remove(base + i);
    }
    collectSave(
        n,
        new CollectInfo(bodyInfo->d_freeVars, boundVars, bodyInfo->d_size + 1));
    return;
  }

  if (isForbidden(n))
  {
    collectSave(n, nullptr);
    return;
  }

  if (n.getNumChildren() == 0)
  {
    collectSave(n, new CollectInfo(UIntSet(), UIntSet(), 1));
    return;
  }

  UIntSet freeVars;
  UIntSet boundVars;
  uint32_t size = 1;
  for (const Node& child : n)
  {
    auto it = d_collectCache.find(child);
    Assert(it != d_collectCache.end());
    CollectInfo* childInfo = it->second.get();
    if (childInfo == nullptr)
    {
      collectSave(n, nullptr);
      return;
    }
    freeVars |= childInfo->d_freeVars;
    boundVars |= childInfo->d_boundVars;
    size += childInfo->d_size;
  }

  collectSave(n, new CollectInfo(freeVars, boundVars, size));
  // The arithmetic patterns are only used when they are nested inside other
  // terms: x + 1 is never considered as a pattern, while f(x+1) can be one if
  // arithmetic is not forbidden.
  Kind k = n.getKind();
  bool arith = isArithKind(k);
  if (!freeVars.empty() && boundVars.empty()
      && (!arith || (!d_nestedArithOnly && isMulDivModKind(k))))
  {
    addCandidate(n, freeVars, size);
  }
}

void PatternInference::addCandidate(TNode n,
                                    const UIntSet& freeVars,
                                    uint32_t size)
{
  if (d_noPatterns != nullptr)
  {
    for (const Node& np : *d_noPatterns)
    {
      if (n == np)
      {
        return;
      }
    }
  }
  if (d_candidatesInfo.find(n) == d_candidatesInfo.end())
  {
    d_candidatesInfo.emplace(n, Info(freeVars, size));
    d_candidates.push_back(n);
  }
}

// -------------------------------------------------------------- filters

void PatternInference::filterLoopingPatterns(std::vector<Node>& result)
{
  size_t num = d_candidates.size();
  for (size_t i1 = 0; i1 < num; ++i1)
  {
    TNode n1 = d_candidates[i1];
    auto e1 = d_candidatesInfo.find(n1);
    Assert(e1 != d_candidatesInfo.end());
    const UIntSet& s1 = e1->second.d_freeVars;
    if (!d_blockLoopPatterns)
    {
      result.push_back(n1);
      continue;
    }
    bool smaller = false;
    for (size_t i2 = 0; i2 < num; ++i2)
    {
      if (i1 == i2)
      {
        continue;
      }
      TNode n2 = d_candidates[i2];
      auto e2 = d_candidatesInfo.find(n2);
      if (e2 == d_candidatesInfo.end())
      {
        continue;
      }
      const UIntSet& s2 = e2->second.d_freeVars;
      // The comparison only makes sense if both terms contain the same
      // variables, e.g. (f X Y) <: (f (g X Z W) Y).
      if (s1 == s2 && d_le(d_baseLevel, d_numBindings, n1, n2)
          && !d_le(d_baseLevel, d_numBindings, n2, n1))
      {
        smaller = true;
        break;
      }
    }
    if (!smaller)
    {
      result.push_back(n1);
    }
    else
    {
      d_candidatesInfo.erase(n1);
    }
  }
}

bool PatternInference::containsSubpattern(TNode n)
{
  auto e = d_candidatesInfo.find(n);
  Assert(e != d_candidatesInfo.end());
  const UIntSet& s1 = e->second.d_freeVars;
  std::unordered_set<TNode> processed;
  std::vector<TNode> todo{n};
  processed.insert(n);
  while (!todo.empty())
  {
    TNode curr = todo.back();
    todo.pop_back();
    if (isVar(curr) || isQuantifier(curr))
    {
      continue;
    }
    if (curr != n)
    {
      auto e2 = d_candidatesInfo.find(curr);
      if (e2 != d_candidatesInfo.end())
      {
        const UIntSet& s2 = e2->second.d_freeVars;
        Assert(s2.subsetOf(s1));
        if (s1 == s2)
        {
          return true;
        }
      }
    }
    for (const Node& c : curr)
    {
      if (processed.insert(c).second)
      {
        todo.push_back(c);
      }
    }
  }
  return false;
}

void PatternInference::filterBiggerPatterns(const std::vector<Node>& patterns,
                                            std::vector<Node>& result)
{
  for (const Node& curr : patterns)
  {
    if (!containsSubpattern(curr))
    {
      result.push_back(curr);
    }
  }
}

bool PatternInference::PatternWeightLt::operator()(TNode n1, TNode n2) const
{
  auto e1 = d_candidatesInfo.find(n1);
  auto e2 = d_candidatesInfo.find(n2);
  Assert(e1 != d_candidatesInfo.end());
  Assert(e2 != d_candidatesInfo.end());
  const Info& i1 = e1->second;
  const Info& i2 = e2->second;
  size_t numFreeVars1 = i1.d_freeVars.size();
  size_t numFreeVars2 = i2.d_freeVars.size();
  return numFreeVars1 > numFreeVars2
         || (numFreeVars1 == numFreeVars2 && i1.d_size < i2.d_size);
}

// -------------------------------------------------- building the patterns

Node PatternInference::mkPattern(TNode candidate)
{
  if (!d_decomposePatterns)
  {
    return d_nm->mkNode(Kind::INST_PATTERN, candidate);
  }
  auto hasVarArg = [](TNode e) {
    if (isVar(e) || isQuantifier(e))
    {
      return false;
    }
    for (const Node& arg : e)
    {
      if (isVar(arg))
      {
        return true;
      }
    }
    return false;
  };
  if (hasVarArg(candidate))
  {
    return d_nm->mkNode(Kind::INST_PATTERN, candidate);
  }
  d_args.clear();
  for (const Node& arg : candidate)
  {
    if (isVar(arg) || isQuantifier(arg))
    {
      return d_nm->mkNode(Kind::INST_PATTERN, candidate);
    }
    d_args.push_back(arg);
  }
  for (size_t i = 0; i < d_args.size(); ++i)
  {
    Node arg = d_args[i];
    if (hasVarArg(arg))
    {
      continue;
    }
    d_args[i] = d_args.back();
    --i;
    d_args.pop_back();

    if (!expr::hasBoundVar(arg))
    {
      continue;
    }
    for (const Node& e : arg)
    {
      if (isVar(e) || isQuantifier(e))
      {
        return d_nm->mkNode(Kind::INST_PATTERN, candidate);
      }
      d_args.push_back(e);
    }
  }
  if (d_args.empty())
  {
    return d_nm->mkNode(Kind::INST_PATTERN, candidate);
  }
  return d_nm->mkNode(Kind::INST_PATTERN, d_args);
}

void PatternInference::candidates2UnaryPatterns(
    const std::vector<Node>& candidates,
    std::vector<Node>& remaining,
    std::vector<Node>& result)
{
  for (const Node& candidate : candidates)
  {
    auto e = d_candidatesInfo.find(candidate);
    Assert(e != d_candidatesInfo.end());
    if (e->second.d_freeVars.size() == d_numBindings)
    {
      result.push_back(mkPattern(candidate));
    }
    else
    {
      remaining.push_back(candidate);
    }
  }
}

void PatternInference::candidates2MultiPatterns(
    size_t maxNumPatterns,
    const std::vector<Node>& candidates,
    std::vector<Node>& result)
{
  // The number of case splits is capped, since this is too inefficient when
  // there are many candidates.
  constexpr size_t s_maxSplits = 32;
  Assert(!candidates.empty());
  d_prePatterns.push_back(std::unique_ptr<PrePattern>(new PrePattern()));
  size_t sz = candidates.size();
  size_t numSplits = 0;
  for (size_t j = 0; j < d_prePatterns.size(); ++j)
  {
    PrePattern* curr = d_prePatterns[j].get();
    if (curr == nullptr)
    {
      continue;
    }
    if (curr->d_freeVars.size() == d_numBindings)
    {
      result.push_back(d_nm->mkNode(Kind::INST_PATTERN, curr->d_exprs));
      if (result.size() >= maxNumPatterns)
      {
        return;
      }
    }
    else if (curr->d_idx < sz)
    {
      TNode n = candidates[curr->d_idx];
      auto e = d_candidatesInfo.find(n);
      Assert(e != d_candidatesInfo.end());
      const UIntSet& s = e->second.d_freeVars;
      if (!s.subsetOf(curr->d_freeVars))
      {
        std::unique_ptr<PrePattern> newP(new PrePattern(*curr));
        newP->d_exprs.push_back(n);
        newP->d_freeVars |= s;
        newP->d_idx++;
        d_prePatterns.push_back(std::move(newP));

        if (numSplits < s_maxSplits)
        {
          std::unique_ptr<PrePattern> keep = std::move(d_prePatterns[j]);
          keep->d_idx++;
          d_prePatterns.push_back(std::move(keep));
          numSplits++;
        }
      }
      else
      {
        std::unique_ptr<PrePattern> keep = std::move(d_prePatterns[j]);
        keep->d_idx++;
        d_prePatterns.push_back(std::move(keep));
      }
    }
  }
}

bool PatternInference::isForbidden(TNode n) const
{
  if (!expr::hasBoundVar(n))
  {
    return false;
  }
  // Z3 never uses a skolem symbol in a pattern, since it does not occur
  // outside of the quantifier and so the pattern would never match.
  if (d_params.d_piAvoidSkolems && isSkolemApp(n))
  {
    return true;
  }
  Kind k = n.getKind();
  if (isCoreKind(k))
  {
    return true;
  }
  return d_forbidArith && isArithKind(k);
}

bool PatternInference::hasPreferredPatterns(
    const std::vector<Node>& /*candidates*/, std::vector<Node>& /*result*/)
{
  // Z3 populates its preferred set from the theory plugins (the datatype
  // recognizers), which this port does not do, so the set is always empty.
  return false;
}

void PatternInference::mkPatterns(size_t baseLevel,
                                  size_t numBindings,
                                  TNode n,
                                  const std::vector<Node>& noPatterns,
                                  std::vector<Node>& result)
{
  d_baseLevel = baseLevel;
  d_numBindings = numBindings;
  d_noPatterns = noPatterns.empty() ? nullptr : &noPatterns;

  collect(n);

  if (!d_candidates.empty())
  {
    d_tmp1.clear();
    filterLoopingPatterns(d_tmp1);
    Assert(!d_tmp1.empty());
    if (!hasPreferredPatterns(d_tmp1, result))
    {
      d_tmp2.clear();
      filterBiggerPatterns(d_tmp1, d_tmp2);
      Assert(!d_tmp2.empty());
      d_tmp1.clear();
      candidates2UnaryPatterns(d_tmp2, d_tmp1, result);
      size_t numExtraMultiPatterns = d_params.d_piMaxMultiPatterns;
      if (result.empty())
      {
        numExtraMultiPatterns++;
      }
      if (numExtraMultiPatterns > 0 && !d_tmp1.empty())
      {
        // the order is not total, hence the stable sort
        std::stable_sort(d_tmp1.begin(), d_tmp1.end(), d_patternWeightLt);
        candidates2MultiPatterns(numExtraMultiPatterns, d_tmp1, result);
      }
    }
  }

  d_prePatterns.clear();
  d_candidatesInfo.clear();
  d_candidates.clear();
  d_noPatterns = nullptr;
}

// ------------------------------------------------------ reduce quantifier

Node PatternInference::reduceQuantifier(TNode q, TNode newBody)
{
  auto rebuild = [&](const std::vector<Node>& patterns) {
    std::vector<Node> annotations;
    if (q.getNumChildren() == 3)
    {
      for (const Node& a : q[2])
      {
        annotations.push_back(a);
      }
    }
    for (const Node& p : patterns)
    {
      annotations.push_back(p);
    }
    if (annotations.empty())
    {
      return d_nm->mkNode(q.getKind(), q[0], newBody);
    }
    return d_nm->mkNode(q.getKind(),
                        q[0],
                        newBody,
                        d_nm->mkNode(Kind::INST_PATTERN_LIST, annotations));
  };

  if (q.getKind() != Kind::FORALL)
  {
    return newBody == q[1] ? Node(q) : rebuild({});
  }

  uint32_t weight = getWeight(q);

  // Nothing to do if the user already supplied a pattern.
  std::vector<Node> noPatterns;
  if (q.getNumChildren() == 3)
  {
    for (const Node& a : q[2])
    {
      if (a.getKind() == Kind::INST_PATTERN)
      {
        return newBody == q[1] ? Node(q) : rebuild({});
      }
      if (a.getKind() == Kind::INST_NO_PATTERN)
      {
        for (const Node& t : a)
        {
          noPatterns.push_back(t);
        }
      }
    }
  }

  if (d_params.d_piNopatWeight >= 0)
  {
    weight = static_cast<uint32_t>(d_params.d_piNopatWeight);
  }

  size_t numDecls = getNumDecls(q);
  size_t baseLevel = varIndex(q[0][0]);
  std::vector<Node> newPatterns;

  bool savedForbidArith = d_forbidArith;
  if (d_params.d_piArith == Params::AP_CONSERVATIVE)
  {
    d_forbidArith = true;
  }
  mkPatterns(baseLevel, numDecls, newBody, noPatterns, newPatterns);

  if (newPatterns.empty() && !noPatterns.empty())
  {
    std::vector<Node> none;
    mkPatterns(baseLevel, numDecls, newBody, none, newPatterns);
    if (d_params.d_piWarnings && !newPatterns.empty())
    {
      std::stringstream ss;
      ss << "ignoring nopats annotation because no other pattern was found "
            "(quantifier id: "
         << getQid(q) << ")";
      Warning() << ss.str() << std::endl;
    }
  }

  if (d_params.d_piArith == Params::AP_CONSERVATIVE)
  {
    d_forbidArith = savedForbidArith;
    if (newPatterns.empty())
    {
      // allow the looping patterns
      bool savedBlock = d_blockLoopPatterns;
      d_blockLoopPatterns = false;
      mkPatterns(baseLevel, numDecls, newBody, noPatterns, newPatterns);
      d_blockLoopPatterns = savedBlock;
      if (!newPatterns.empty())
      {
        weight = std::max(weight, d_params.d_piArithWeight);
      }
    }
  }

  if (d_params.d_piArith != Params::AP_NO && newPatterns.empty())
  {
    // try to find a non-nested arithmetic pattern, allowing the looping ones
    bool savedNested = d_nestedArithOnly;
    bool savedBlock = d_blockLoopPatterns;
    d_nestedArithOnly = false;
    d_blockLoopPatterns = false;
    mkPatterns(baseLevel, numDecls, newBody, noPatterns, newPatterns);
    d_nestedArithOnly = savedNested;
    d_blockLoopPatterns = savedBlock;
    if (!newPatterns.empty())
    {
      weight = std::max(weight, d_params.d_piNonNestedArithWeight);
    }
  }

  if (newPatterns.empty())
  {
    if (d_params.d_piWarnings)
    {
      std::stringstream ss;
      ss << "failed to find a pattern for quantifier (quantifier id: "
         << getQid(q) << ")";
      Warning() << ss.str() << std::endl;
    }
    if (newBody == q[1])
    {
      return q;
    }
  }

  Node newQ = rebuild(newPatterns);
  if (weight != getWeight(newQ))
  {
    setWeight(newQ, weight);
  }
  Trace("z3-pattern-inference")
      << "inferred patterns for " << q << ": " << newQ << std::endl;
  return newQ;
}

}  // namespace z3
}  // namespace cvc5::internal
