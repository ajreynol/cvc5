/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An incomplete model checker for quantifiers.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), file
 * src/smt/smt_quick_checker.cpp, and recast in cvc5 style.
 */

#include "z3/quick_checker.h"

#include "expr/node_algorithm.h"
#include "expr/node_manager.h"
#include "z3/ast.h"
#include "z3/enode.h"
#include "z3/smt_context.h"
#include "z3/util/util.h"

namespace cvc5::internal {
namespace z3 {

namespace {

/** True if a and b are distinct constants. */
bool areDistinct(TNode a, TNode b)
{
  return a.isConst() && b.isConst() && a != b;
}

/** The kinds Z3 treats as its basic family in the structural check. */
bool isCoreKind(Kind k)
{
  switch (k)
  {
    case Kind::NOT:
    case Kind::AND:
    case Kind::OR:
    case Kind::ITE:
    case Kind::EQUAL:
    case Kind::CONST_BOOLEAN: return true;
    default: return false;
  }
}

}  // namespace

// ------------------------------------------------------------- collector

QuickChecker::Collector::Collector(SmtContext& c)
    : d_context(c), d_conservative(true), d_numVars(0)
{
}

void QuickChecker::Collector::init(TNode q)
{
  d_numVars = getNumDecls(q);
  d_alreadyFound.assign(d_numVars + 1, false);
  d_candidates.resize(d_numVars + 1);
  d_tmpCandidates.resize(d_numVars + 1);
  for (size_t i = 0; i < d_numVars; ++i)
  {
    d_candidates[i].clear();
  }
  d_cache.clear();
}

bool QuickChecker::Collector::checkArg(ENode* n, TNode f, size_t i)
{
  if (f.isNull() || !d_conservative)
  {
    return true;
  }
  for (ENode* curr : d_context.enodesOf(f))
  {
    if (d_context.isRelevant(curr) && curr->isCgr() && i < curr->getNumArgs()
        && curr->getArg(i)->getRoot() == n->getRoot())
    {
      return true;
    }
  }
  return false;
}

void QuickChecker::Collector::collectCore(TNode n, TNode p, size_t i)
{
  TNode f = getDecl(n);
  size_t numArgs = n.getNumChildren();
  for (size_t j = 0; j < numArgs; ++j)
  {
    TNode arg = n[j];
    if (!isVar(arg))
    {
      // Z3 only passes the parent on when it is not a Boolean connective.
      if (!isCoreKind(n.getKind()))
      {
        collect(arg, getDecl(n), j);
      }
      else
      {
        collect(arg, TNode::null(), 0);
      }
      continue;
    }
    uint32_t idx = varIndex(arg);
    if (idx >= d_numVars)
    {
      return;
    }
    if (d_alreadyFound[idx] && d_conservative)
    {
      ENodeSet& s = d_candidates[idx];
      ENodeSet& ns = d_tmpCandidates[idx];
      if (s.empty())
      {
        continue;
      }
      ns.clear();
      for (ENode* curr : d_context.enodesOf(f))
      {
        if (d_context.isRelevant(curr) && curr->isCgr() && checkArg(curr, p, i)
            && j < curr->getNumArgs())
        {
          ENode* carg = curr->getArg(j)->getRoot();
          // the intersection with what was already found
          if (s.count(carg) != 0)
          {
            ns.insert(carg);
          }
        }
      }
      s.swap(ns);
    }
    else
    {
      d_alreadyFound[idx] = true;
      ENodeSet& s = d_candidates[idx];
      for (ENode* curr : d_context.enodesOf(f))
      {
        if (d_context.isRelevant(curr) && curr->isCgr() && checkArg(curr, p, i)
            && j < curr->getNumArgs())
        {
          s.insert(curr->getArg(j)->getRoot());
        }
      }
    }
  }
}

void QuickChecker::Collector::collect(TNode n, TNode f, size_t idx)
{
  if (isQuantifier(n) || isVar(n) || !expr::hasBoundVar(n))
  {
    return;
  }
  Entry e{n, f, idx};
  if (!d_cache.insert(e).second)
  {
    return;
  }
  collectCore(n, f, idx);
}

void QuickChecker::Collector::saveResult(
    std::vector<ENodeVector>& candidates)
{
  candidates.resize(d_numVars + 1);
  for (size_t i = 0; i < d_numVars; ++i)
  {
    ENodeVector& v = candidates[i];
    v.clear();
    for (ENode* curr : d_candidates[i])
    {
      v.push_back(curr);
    }
  }
}

void QuickChecker::Collector::operator()(
    TNode q, bool conservative, std::vector<ENodeVector>& candidates)
{
  bool saved = d_conservative;
  d_conservative = conservative;
  init(q);
  collect(getQuantBody(q), TNode::null(), 0);
  saveResult(candidates);
  d_conservative = saved;
}

// --------------------------------------------------------- quick checker

QuickChecker::QuickChecker(SmtContext& c)
    : d_context(c), d_collector(c), d_numBindings(0)
{
}

bool QuickChecker::instantiateUnsat(TNode q)
{
  d_candidateVectors.clear();
  d_collector(q, true, d_candidateVectors);
  d_numBindings = getNumDecls(q);
  return processCandidates(q, true);
}

bool QuickChecker::instantiateNotSat(TNode q)
{
  d_candidateVectors.clear();
  d_collector(q, false, d_candidateVectors);
  d_numBindings = getNumDecls(q);
  return processCandidates(q, false);
}

bool QuickChecker::processCandidates(TNode q, bool unsat)
{
  std::vector<std::pair<ENode*, ENode*>> emptyUsedENodes;
  std::vector<size_t> szs;
  std::vector<size_t> it;
  for (size_t i = 0; i < d_numBindings; ++i)
  {
    size_t sz = d_candidateVectors[i].size();
    if (sz == 0)
    {
      return false;
    }
    szs.push_back(sz);
    it.push_back(0);
  }
  bool result = false;
  d_bindings.resize(d_numBindings + 1, nullptr);
  do
  {
    // The bindings are indexed by de Bruijn level, which is declaration
    // order, so unlike Z3 there is nothing to reverse here.
    for (size_t i = 0; i < d_numBindings; ++i)
    {
      d_bindings[i] = d_candidateVectors[i][it[i]];
    }
    if (d_context.containsInstance(q, d_numBindings, d_bindings.data()))
    {
      continue;
    }
    bool isCandidate =
        unsat ? checkQuantifier(q, false) : !checkQuantifier(q, true);
    if (!isCandidate)
    {
      continue;
    }
    uint32_t maxGeneration =
        d_context.getMaxGeneration(d_numBindings, d_bindings.data());
    if (d_context.addInstance(q,
                              TNode::null(), /* no pattern was used */
                              d_numBindings,
                              d_bindings.data(),
                              maxGeneration,
                              0, /* the top generations are only available */
                              0, /* for the instances the MAM creates */
                              emptyUsedENodes))
    {
      result = true;
    }
  } while (productIteratorNext(szs.size(), szs.data(), it.data()));
  return result;
}

bool QuickChecker::checkQuantifier(TNode q, bool isTrue)
{
  bool r = check(getQuantBody(q), isTrue);
  d_checkCache.clear();
  d_canonizeCache.clear();
  return r;
}

bool QuickChecker::allArgs(TNode a, bool isTrue)
{
  for (const Node& arg : a)
  {
    if (!check(arg, isTrue))
    {
      return false;
    }
  }
  return true;
}

bool QuickChecker::anyArg(TNode a, bool isTrue)
{
  for (const Node& arg : a)
  {
    if (check(arg, isTrue))
    {
      return true;
    }
  }
  return false;
}

bool QuickChecker::checkCore(TNode n, bool isTrue)
{
  Assert(n.getType().isBoolean());
  if (d_context.bInternalized(n) && d_context.isRelevant(n))
  {
    LBool val = d_context.getAssignment(n);
    return val != L_UNDEF && isTrue == (val == L_TRUE);
  }
  if (isQuantifier(n) || isVar(n))
  {
    return false;
  }
  switch (n.getKind())
  {
    case Kind::CONST_BOOLEAN:
      return n.getConst<bool>() ? isTrue : !isTrue;
    case Kind::NOT: return check(n[0], !isTrue);
    case Kind::OR: return isTrue ? anyArg(n, true) : allArgs(n, false);
    case Kind::AND: return isTrue ? allArgs(n, true) : anyArg(n, false);
    case Kind::ITE:
      if (check(n[0], true))
      {
        return check(n[1], isTrue);
      }
      if (check(n[0], false))
      {
        return check(n[2], isTrue);
      }
      return check(n[1], isTrue) && check(n[2], isTrue);
    case Kind::EQUAL:
    {
      if (n[0].getType().isBoolean())
      {
        if (isTrue)
        {
          return (check(n[0], true) && check(n[1], true))
                 || (check(n[0], false) && check(n[1], false));
        }
        return (check(n[0], true) && check(n[1], false))
               || (check(n[0], false) && check(n[1], true));
      }
      Node lhs = canonize(n[0]);
      Node rhs = canonize(n[1]);
      if (isTrue)
      {
        return lhs == rhs;
      }
      if (d_context.eInternalized(lhs) && d_context.isRelevant(lhs)
          && d_context.eInternalized(rhs) && d_context.isRelevant(rhs)
          && d_context.getENode(lhs)->getRoot()
                 != d_context.getENode(rhs)->getRoot())
      {
        return true;
      }
      return areDistinct(lhs, rhs);
    }
    default: break;
  }
  Node newN = canonize(n);
  if (d_context.litInternalized(newN) && d_context.isRelevant(newN))
  {
    LBool val = d_context.getAssignment(newN);
    if (val != L_UNDEF)
    {
      return isTrue == (val == L_TRUE);
    }
  }
  if (newN.getKind() == Kind::CONST_BOOLEAN)
  {
    return isTrue == newN.getConst<bool>();
  }
  return false;
}

bool QuickChecker::check(TNode n, bool isTrue)
{
  std::pair<Node, bool> p(n, isTrue);
  auto it = d_checkCache.find(p);
  if (it != d_checkCache.end())
  {
    return it->second;
  }
  bool r = checkCore(n, isTrue);
  d_checkCache[p] = r;
  return r;
}

Node QuickChecker::canonize(TNode n)
{
  if (isVar(n))
  {
    uint32_t idx = varIndex(n);
    if (idx >= d_numBindings)
    {
      return n;
    }
    return d_bindings[idx]->getRoot()->getExpr();
  }
  if (d_context.eInternalized(n))
  {
    return d_context.getENode(n)->getRoot()->getExpr();
  }
  if (isQuantifier(n) || n.getNumChildren() == 0)
  {
    return n;
  }
  auto it = d_canonizeCache.find(n);
  if (it != d_canonizeCache.end())
  {
    return it->second;
  }
  bool hasArgENodes = true;
  std::vector<Node> newArgs;
  ENodeVector newArgENodes;
  for (const Node& arg : n)
  {
    Node newArg = canonize(arg);
    newArgs.push_back(newArg);
    if (d_context.eInternalized(newArg))
    {
      newArgENodes.push_back(d_context.getENode(newArg));
    }
    else
    {
      hasArgENodes = false;
    }
  }
  if (hasArgENodes)
  {
    ENode* e = d_context.getENodeEqTo(getDecl(n),
                                      isCommutative(n),
                                      newArgENodes.size(),
                                      newArgENodes.data());
    if (e != nullptr)
    {
      Node r = e->getRoot()->getExpr();
      d_canonizeCache[n] = r;
      return r;
    }
  }
  // substitute the values of the model
  for (size_t i = 0, sz = newArgs.size(); i < sz; ++i)
  {
    if (!d_context.eInternalized(newArgs[i]))
    {
      continue;
    }
    Node newValue;
    if (d_context.getValue(d_context.getENode(newArgs[i]), newValue))
    {
      newArgs[i] = newValue;
    }
  }
  NodeManager* nm = n.getNodeManager();
  std::vector<Node> children;
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    children.push_back(n.getOperator());
  }
  children.insert(children.end(), newArgs.begin(), newArgs.end());
  Node newExpr = d_context.rewriteInstance(nm->mkNode(n.getKind(), children));
  d_canonizeCache[n] = newExpr;
  return newExpr;
}

}  // namespace z3
}  // namespace cvc5::internal
