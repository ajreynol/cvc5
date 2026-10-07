/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Pattern inference for eager E-matching.
 */

#include "theory/quantifiers/eager/pattern_inference.h"

#include <algorithm>

#include "expr/node_algorithm.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

/** The number of extra multi-patterns z3 creates by default
 * (pi.max_multi_patterns) */
static const size_t s_maxMultiPatterns = 0;
/** Limit on the case splits of the multi-pattern search. z3: MAX_SPLITS */
static const size_t s_maxSplits = 32;

PatternInference::PatternInference(Env& env)
    : EnvObj(env),
      d_numBindings(0),
      d_forbidArith(true),
      d_nestedArithOnly(true),
      d_blockLoopPatterns(true),
      d_decomposePatterns(true),
      d_maxMultiPatterns(s_maxMultiPatterns)
{
}

PatternInference::~PatternInference() {}

bool PatternInference::isArith(TNode n)
{
  switch (n.getKind())
  {
    case Kind::ADD:
    case Kind::SUB:
    case Kind::NEG:
    case Kind::MULT:
    case Kind::NONLINEAR_MULT:
    case Kind::DIVISION:
    case Kind::DIVISION_TOTAL:
    case Kind::INTS_DIVISION:
    case Kind::INTS_DIVISION_TOTAL:
    case Kind::INTS_MODULUS:
    case Kind::INTS_MODULUS_TOTAL:
    case Kind::ABS:
    case Kind::POW:
    case Kind::POW2:
    case Kind::TO_REAL:
    case Kind::TO_INTEGER:
    case Kind::IS_INTEGER:
    case Kind::DIVISIBLE:
    case Kind::LT:
    case Kind::LEQ:
    case Kind::GT:
    case Kind::GEQ: return true;
    default: return false;
  }
}

bool PatternInference::isArithCandidateKind(Kind k) const
{
  if (d_nestedArithOnly)
  {
    return false;
  }
  // z3 only allows OP_DIV, OP_IDIV, OP_MOD, OP_REM and OP_MUL as the top symbol
  // of an arithmetic pattern
  switch (k)
  {
    case Kind::DIVISION:
    case Kind::DIVISION_TOTAL:
    case Kind::INTS_DIVISION:
    case Kind::INTS_DIVISION_TOTAL:
    case Kind::INTS_MODULUS:
    case Kind::INTS_MODULUS_TOTAL:
    case Kind::MULT:
    case Kind::NONLINEAR_MULT: return true;
    default: return false;
  }
}

bool PatternInference::isForbidden(TNode n) const
{
  // z3: a ground term is never forbidden, since matching never has to look
  // inside it
  if (!expr::hasBoundVar(n))
  {
    return false;
  }
  // the operators of z3's basic family, which is forbidden except for true and
  // false
  switch (n.getKind())
  {
    case Kind::NOT:
    case Kind::AND:
    case Kind::OR:
    case Kind::IMPLIES:
    case Kind::XOR:
    case Kind::ITE:
    case Kind::EQUAL:
    case Kind::DISTINCT: return true;
    default: break;
  }
  if (d_forbidArith && isArith(n))
  {
    return true;
  }
  // z3 never uses a skolem function in a pattern, since a term built from it
  // does not occur outside the quantifier (pi.avoid_skolems)
  if (n.hasOperator() && n.getOperator().getKind() == Kind::SKOLEM)
  {
    return true;
  }
  return false;
}

void PatternInference::addCandidate(TNode n,
                                    const VarSet& freeVars,
                                    size_t size)
{
  for (const Node& np : d_noPatterns)
  {
    if (n == np)
    {
      return;
    }
  }
  if (d_candidateInfo.find(n) == d_candidateInfo.end())
  {
    d_candidateInfo[n] = std::pair<VarSet, size_t>(freeVars, size);
    d_candidates.push_back(n);
  }
}

void PatternInference::saveCandidate(TNode n)
{
  Info info;
  std::map<Node, size_t>::const_iterator itv = d_varIndex.find(n);
  if (itv != d_varIndex.end())
  {
    // a variable of the quantifier
    info.d_freeVars.insert(itv->second);
    info.d_size = 1;
    d_info[n] = info;
    return;
  }
  if (n.getKind() == Kind::BOUND_VARIABLE)
  {
    // a variable bound inside the body
    info.d_hasForeignVar = true;
    info.d_size = 1;
    d_info[n] = info;
    return;
  }
  if (n.isClosure())
  {
    // z3 keeps the free variables of the body and drops the variables this
    // closure binds from the ones bound inside
    std::map<Node, Info>::const_iterator itb = d_info.find(n[1]);
    Assert(itb != d_info.end());
    const Info& bi = itb->second;
    if (!bi.d_valid)
    {
      info.d_valid = false;
      d_info[n] = info;
      return;
    }
    info.d_freeVars = bi.d_freeVars;
    info.d_size = bi.d_size + 1;
    std::unordered_set<Node> fvs;
    expr::getFreeVariables(n, fvs);
    for (const Node& v : fvs)
    {
      if (d_varIndex.find(v) == d_varIndex.end())
      {
        info.d_hasForeignVar = true;
        break;
      }
    }
    d_info[n] = info;
    return;
  }
  if (isForbidden(n))
  {
    info.d_valid = false;
    d_info[n] = info;
    return;
  }
  if (n.getNumChildren() == 0)
  {
    info.d_size = 1;
    d_info[n] = info;
    return;
  }
  info.d_size = 1;
  for (const Node& nc : n)
  {
    std::map<Node, Info>::const_iterator itc = d_info.find(nc);
    Assert(itc != d_info.end());
    const Info& ci = itc->second;
    if (!ci.d_valid)
    {
      Info bad;
      bad.d_valid = false;
      d_info[n] = bad;
      return;
    }
    info.d_freeVars.insert(ci.d_freeVars.begin(), ci.d_freeVars.end());
    info.d_hasForeignVar = info.d_hasForeignVar || ci.d_hasForeignVar;
    info.d_size += ci.d_size;
  }
  d_info[n] = info;
  // Arithmetic patterns are only used when nested inside another term: x + 1 is
  // never a pattern, while f(x + 1) can be if arithmetic is not forbidden.
  if (!info.d_freeVars.empty() && !info.d_hasForeignVar
      && (!isArith(n) || isArithCandidateKind(n.getKind())))
  {
    addCandidate(n, info.d_freeVars, info.d_size);
  }
}

void PatternInference::collect(TNode body)
{
  // post-order traversal of the body, including under closures
  std::vector<std::pair<TNode, bool>> visit{{body, false}};
  std::unordered_set<TNode> done;
  while (!visit.empty())
  {
    TNode n = visit.back().first;
    if (done.find(n) != done.end())
    {
      visit.pop_back();
      continue;
    }
    if (!visit.back().second)
    {
      visit.back().second = true;
      if (n.isClosure())
      {
        visit.push_back({n[1], false});
        continue;
      }
      for (const Node& nc : n)
      {
        visit.push_back({nc, false});
      }
      continue;
    }
    visit.pop_back();
    done.insert(n);
    saveCandidate(n);
  }
}

bool PatternInference::isSmallerPattern(TNode p1, TNode p2) const
{
  // z3: smaller_pattern::process
  std::map<Node, Node> bindings;
  std::set<std::pair<Node, Node>> cache;
  std::vector<std::pair<Node, Node>> todo{{p1, p2}};
  while (!todo.empty())
  {
    std::pair<Node, Node> curr = todo.back();
    todo.pop_back();
    if (!cache.insert(curr).second)
    {
      continue;
    }
    TNode a = curr.first;
    TNode b = curr.second;
    if (d_varIndex.find(a) != d_varIndex.end())
    {
      std::map<Node, Node>::const_iterator it = bindings.find(a);
      if (it == bindings.end())
      {
        bindings[a] = b;
      }
      else if (it->second != b)
      {
        return false;
      }
      continue;
    }
    if (a.getKind() != b.getKind() || a.getNumChildren() != b.getNumChildren())
    {
      return false;
    }
    if (a.getNumChildren() == 0)
    {
      if (a != b)
      {
        return false;
      }
      continue;
    }
    if (a.hasOperator() != b.hasOperator()
        || (a.hasOperator() && a.getOperator() != b.getOperator()))
    {
      return false;
    }
    for (size_t i = 0, nargs = a.getNumChildren(); i < nargs; i++)
    {
      todo.push_back({a[i], b[i]});
    }
  }
  return true;
}

void PatternInference::filterLoopingPatterns(std::vector<Node>& result)
{
  // z3: pattern_inference_cfg::filter_looping_patterns
  size_t num = d_candidates.size();
  for (size_t i1 = 0; i1 < num; i1++)
  {
    TNode n1 = d_candidates[i1];
    std::map<Node, std::pair<VarSet, size_t>>::const_iterator e1 =
        d_candidateInfo.find(n1);
    Assert(e1 != d_candidateInfo.end());
    const VarSet& s1 = e1->second.first;
    if (!d_blockLoopPatterns)
    {
      result.push_back(n1);
      continue;
    }
    bool smaller = false;
    for (size_t i2 = 0; i2 < num; i2++)
    {
      if (i1 == i2)
      {
        continue;
      }
      TNode n2 = d_candidates[i2];
      std::map<Node, std::pair<VarSet, size_t>>::const_iterator e2 =
          d_candidateInfo.find(n2);
      if (e2 == d_candidateInfo.end())
      {
        continue;
      }
      // the comparison only makes sense for candidates with the same variables
      if (e2->second.first == s1 && isSmallerPattern(n1, n2)
          && !isSmallerPattern(n2, n1))
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
      d_candidateInfo.erase(n1);
    }
  }
}

bool PatternInference::containsSubpattern(TNode n) const
{
  // z3: pattern_inference_cfg::contains_subpattern
  std::map<Node, std::pair<VarSet, size_t>>::const_iterator e =
      d_candidateInfo.find(n);
  Assert(e != d_candidateInfo.end());
  const VarSet& s1 = e->second.first;
  std::vector<TNode> visit{n};
  std::unordered_set<TNode> visited;
  while (!visit.empty())
  {
    TNode curr = visit.back();
    visit.pop_back();
    if (!visited.insert(curr).second)
    {
      continue;
    }
    if (curr.isClosure() || curr.getKind() == Kind::BOUND_VARIABLE)
    {
      continue;
    }
    if (curr != n)
    {
      std::map<Node, std::pair<VarSet, size_t>>::const_iterator ec =
          d_candidateInfo.find(curr);
      if (ec != d_candidateInfo.end() && ec->second.first == s1)
      {
        return true;
      }
    }
    for (const Node& cc : curr)
    {
      visit.push_back(cc);
    }
  }
  return false;
}

void PatternInference::filterBiggerPatterns(const std::vector<Node>& patterns,
                                            std::vector<Node>& result)
{
  // z3: pattern_inference_cfg::filter_bigger_patterns
  for (const Node& curr : patterns)
  {
    if (!containsSubpattern(curr))
    {
      result.push_back(curr);
    }
  }
}

bool PatternInference::patternWeightLt(TNode n1, TNode n2) const
{
  // z3: pattern_weight_lt
  std::map<Node, std::pair<VarSet, size_t>>::const_iterator e1 =
      d_candidateInfo.find(n1);
  std::map<Node, std::pair<VarSet, size_t>>::const_iterator e2 =
      d_candidateInfo.find(n2);
  Assert(e1 != d_candidateInfo.end() && e2 != d_candidateInfo.end());
  size_t nfv1 = e1->second.first.size();
  size_t nfv2 = e2->second.first.size();
  return nfv1 > nfv2 || (nfv1 == nfv2 && e1->second.second < e2->second.second);
}

Node PatternInference::mkPattern(const std::vector<Node>& terms)
{
  Assert(!terms.empty());
  return nodeManager()->mkNode(Kind::INST_PATTERN, terms);
}

Node PatternInference::mkPattern(TNode candidate)
{
  // z3: pattern_inference_cfg::mk_pattern
  std::vector<Node> one{candidate};
  if (!d_decomposePatterns)
  {
    return mkPattern(one);
  }
  // whether some argument of e is a variable of the quantifier
  auto hasVarArg = [this](TNode e) {
    if (e.getNumChildren() == 0)
    {
      return false;
    }
    for (const Node& arg : e)
    {
      if (d_varIndex.find(arg) != d_varIndex.end())
      {
        return true;
      }
    }
    return false;
  };
  if (hasVarArg(candidate))
  {
    return mkPattern(one);
  }
  // z3 gives up on decomposition if an argument is not an application, i.e. is
  // a variable or a quantifier
  auto isNotApp = [](TNode e) {
    return e.getKind() == Kind::BOUND_VARIABLE || e.isClosure();
  };
  std::vector<Node> args;
  for (const Node& arg : candidate)
  {
    if (isNotApp(arg))
    {
      return mkPattern(one);
    }
    args.push_back(arg);
  }
  for (size_t i = 0; i < args.size(); i++)
  {
    Node arg = args[i];
    if (hasVarArg(arg))
    {
      continue;
    }
    // drop it and push its arguments instead, as z3 does
    args[i] = args.back();
    args.pop_back();
    i--;
    if (!expr::hasBoundVar(arg))
    {
      continue;
    }
    for (const Node& e : arg)
    {
      if (isNotApp(e))
      {
        return mkPattern(one);
      }
      args.push_back(e);
    }
  }
  if (args.empty())
  {
    return mkPattern(one);
  }
  return mkPattern(args);
}

void PatternInference::candidatesToUnaryPatterns(
    const std::vector<Node>& candidates,
    std::vector<Node>& remaining,
    std::vector<Node>& result)
{
  // z3: pattern_inference_cfg::candidates2unary_patterns
  for (const Node& candidate : candidates)
  {
    std::map<Node, std::pair<VarSet, size_t>>::const_iterator e =
        d_candidateInfo.find(candidate);
    Assert(e != d_candidateInfo.end());
    if (e->second.first.size() == d_numBindings)
    {
      result.push_back(mkPattern(candidate));
    }
    else
    {
      remaining.push_back(candidate);
    }
  }
}

void PatternInference::candidatesToMultiPatterns(
    size_t maxNumPatterns,
    const std::vector<Node>& candidates,
    std::vector<Node>& result)
{
  // z3: pattern_inference_cfg::candidates2multi_patterns
  Assert(!candidates.empty());
  std::vector<PrePattern> pre;
  pre.push_back(PrePattern());
  size_t sz = candidates.size();
  size_t numSplits = 0;
  for (size_t j = 0; j < pre.size(); j++)
  {
    PrePattern curr = pre[j];
    if (curr.d_freeVars.size() == d_numBindings)
    {
      result.push_back(mkPattern(curr.d_exprs));
      if (result.size() >= maxNumPatterns)
      {
        return;
      }
      continue;
    }
    if (curr.d_idx >= sz)
    {
      continue;
    }
    TNode n = candidates[curr.d_idx];
    std::map<Node, std::pair<VarSet, size_t>>::const_iterator e =
        d_candidateInfo.find(n);
    Assert(e != d_candidateInfo.end());
    const VarSet& s = e->second.first;
    bool subset = std::includes(
        curr.d_freeVars.begin(), curr.d_freeVars.end(), s.begin(), s.end());
    if (!subset)
    {
      PrePattern newP = curr;
      newP.d_exprs.push_back(n);
      newP.d_freeVars.insert(s.begin(), s.end());
      newP.d_idx++;
      pre.push_back(newP);
      if (numSplits < s_maxSplits)
      {
        curr.d_idx++;
        pre.push_back(curr);
        numSplits++;
      }
    }
    else
    {
      curr.d_idx++;
      pre.push_back(curr);
    }
  }
}

void PatternInference::mkPatterns(TNode q,
                                  TNode body,
                                  const std::vector<Node>& noPatterns,
                                  std::vector<Node>& result)
{
  // z3: pattern_inference_cfg::mk_patterns
  d_numBindings = q[0].getNumChildren();
  d_noPatterns = noPatterns;
  d_info.clear();
  d_candidates.clear();
  d_candidateInfo.clear();
  collect(body);
  if (d_candidates.empty())
  {
    return;
  }
  std::vector<Node> tmp1;
  filterLoopingPatterns(tmp1);
  if (tmp1.empty())
  {
    return;
  }
  std::vector<Node> tmp2;
  filterBiggerPatterns(tmp1, tmp2);
  if (tmp2.empty())
  {
    return;
  }
  tmp1.clear();
  candidatesToUnaryPatterns(tmp2, tmp1, result);
  size_t numExtraMultiPatterns = d_maxMultiPatterns;
  if (result.empty())
  {
    numExtraMultiPatterns++;
  }
  if (numExtraMultiPatterns > 0 && !tmp1.empty())
  {
    // the order is not total, so the sort has to be stable to be reproducible
    std::stable_sort(tmp1.begin(), tmp1.end(), [this](TNode n1, TNode n2) {
      return patternWeightLt(n1, n2);
    });
    candidatesToMultiPatterns(numExtraMultiPatterns, tmp1, result);
  }
}

void PatternInference::getPatterns(TNode q, std::vector<Node>& pats)
{
  Assert(q.getKind() == Kind::FORALL);
  d_varIndex.clear();
  for (size_t i = 0, nvars = q[0].getNumChildren(); i < nvars; i++)
  {
    d_varIndex[q[0][i]] = i;
  }
  std::vector<Node> noPatterns;
  if (q.getNumChildren() == 3)
  {
    for (const Node& p : q[2])
    {
      if (p.getKind() == Kind::INST_NO_PATTERN)
      {
        noPatterns.insert(noPatterns.end(), p.begin(), p.end());
      }
    }
  }
  TNode body = q[1];
  // z3 first tries without arithmetic at all (pi.arith = conservative)
  d_forbidArith = true;
  d_nestedArithOnly = true;
  d_blockLoopPatterns = true;
  mkPatterns(q, body, noPatterns, pats);
  if (pats.empty() && !noPatterns.empty())
  {
    // z3 ignores the nopats annotation rather than give up
    mkPatterns(q, body, {}, pats);
  }
  if (pats.empty())
  {
    // then with arithmetic allowed inside patterns, and looping patterns
    d_forbidArith = false;
    d_blockLoopPatterns = false;
    mkPatterns(q, body, noPatterns, pats);
  }
  if (pats.empty())
  {
    // then with arithmetic applications allowed as patterns themselves
    d_nestedArithOnly = false;
    d_blockLoopPatterns = false;
    mkPatterns(q, body, noPatterns, pats);
  }
  // z3 would now try pulling nested quantifiers (pi.pull_quantifiers); we do
  // not, so a quantifier whose only patterns are under a nested quantifier
  // gets none.
  if (TraceIsOn("eager-pattern"))
  {
    Trace("eager-pattern") << "PatternInference: " << q << std::endl;
    for (const Node& p : pats)
    {
      Trace("eager-pattern") << "  " << p << std::endl;
    }
    if (pats.empty())
    {
      Trace("eager-pattern") << "  (none)" << std::endl;
    }
  }
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
