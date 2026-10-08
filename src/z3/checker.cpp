/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A cheap check of whether an instance is already satisfied or falsified.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_checker.cpp, and recast in cvc5 style.
 */

#include "z3/checker.h"

#include <vector>

#include "z3/ast.h"
#include "z3/enode.h"
#include "z3/smt_context.h"

namespace cvc5::internal {
namespace z3 {

namespace {

/** The depth at which the structural evaluation gives up. */
constexpr size_t s_maxDepth = 600;

bool isTrueNode(TNode n)
{
  return n.getKind() == Kind::CONST_BOOLEAN && n.getConst<bool>();
}

}  // namespace

Checker::Checker(SmtContext& c)
    : d_context(c), d_numBindings(0), d_bindings(nullptr)
{
}

bool Checker::allArgs(TNode a, size_t depth, bool isTrue)
{
  for (const Node& arg : a)
  {
    if (!check(arg, depth + 1, isTrue))
    {
      return false;
    }
  }
  return true;
}

bool Checker::anyArg(TNode a, size_t depth, bool isTrue)
{
  for (const Node& arg : a)
  {
    if (check(arg, depth + 1, isTrue))
    {
      return true;
    }
  }
  return false;
}

bool Checker::checkCore(TNode n, size_t depth, bool isTrue)
{
  if (depth > s_maxDepth)
  {
    return false;
  }
  Assert(n.getType().isBoolean());
  if (d_context.bInternalized(n) && d_context.isRelevant(n))
  {
    LBool val = d_context.getAssignment(n);
    return val != L_UNDEF && isTrue == (val == L_TRUE);
  }
  if (!isApp(n))
  {
    return false;
  }
  switch (n.getKind())
  {
    case Kind::CONST_BOOLEAN: return isTrueNode(n) ? isTrue : !isTrue;
    case Kind::NOT: return check(n[0], depth + 1, !isTrue);
    case Kind::OR:
      return isTrue ? anyArg(n, depth, true) : allArgs(n, depth, false);
    case Kind::AND:
      return isTrue ? allArgs(n, depth, true) : anyArg(n, depth, false);
    case Kind::IMPLIES:
      if (isTrue)
      {
        return check(n[0], depth + 1, false) || check(n[1], depth + 1, true);
      }
      return check(n[0], depth + 1, true) && check(n[1], depth + 1, false);
    case Kind::EQUAL:
      if (!n[0].getType().isBoolean())
      {
        ENode* lhs = getENodeEqTo(n[0]);
        ENode* rhs = getENodeEqTo(n[1]);
        if (lhs != nullptr && rhs != nullptr && d_context.isRelevant(lhs)
            && d_context.isRelevant(rhs))
        {
          if (isTrue && lhs->getRoot() == rhs->getRoot())
          {
            return true;
          }
          if (!isTrue && d_context.isDiseq(lhs, rhs))
          {
            return true;
          }
        }
        return false;
      }
      if (isTrue)
      {
        return (check(n[0], depth + 1, true) && check(n[1], depth + 1, true))
               || (check(n[0], depth + 1, false)
                   && check(n[1], depth + 1, false));
      }
      return (check(n[0], depth + 1, true) && check(n[1], depth + 1, false))
             || (check(n[0], depth + 1, false) && check(n[1], depth + 1, true));
    case Kind::XOR:
      if (isTrue)
      {
        return (check(n[0], depth + 1, true) && check(n[1], depth + 1, false))
               || (check(n[0], depth + 1, false)
                   && check(n[1], depth + 1, true));
      }
      return (check(n[0], depth + 1, true) && check(n[1], depth + 1, true))
             || (check(n[0], depth + 1, false)
                 && check(n[1], depth + 1, false));
    case Kind::ITE:
    {
      if (d_context.litInternalized(n[0]) && d_context.isRelevant(n[0]))
      {
        switch (d_context.getAssignment(n[0]))
        {
          case L_FALSE: return check(n[2], depth + 1, isTrue);
          case L_UNDEF: return false;
          case L_TRUE: return check(n[1], depth + 1, isTrue);
        }
      }
      return check(n[1], depth + 1, isTrue) && check(n[2], depth + 1, isTrue);
    }
    default: break;
  }
  ENode* e = getENodeEqTo(n);
  if (e != nullptr && e->isBool() && d_context.isRelevant(e))
  {
    LBool val = d_context.getAssignment(e->getExpr());
    return val != L_UNDEF && isTrue == (val == L_TRUE);
  }
  return false;
}

bool Checker::check(TNode n, size_t depth, bool isTrue)
{
  std::unordered_map<Node, bool>& cache = d_isTrueCache[isTrue ? 1 : 0];
  auto it = cache.find(n);
  if (it != cache.end())
  {
    return it->second;
  }
  bool r = checkCore(n, depth, isTrue);
  cache[n] = r;
  return r;
}

ENode* Checker::getENodeEqToCore(TNode n)
{
  std::vector<ENode*> buffer;
  size_t num = n.getNumChildren();
  for (size_t i = 0; i < num; ++i)
  {
    ENode* arg = getENodeEqTo(n[i]);
    if (arg == nullptr)
    {
      return nullptr;
    }
    buffer.push_back(arg);
  }
  ENode* e =
      d_context.getENodeEqTo(getDecl(n), isCommutative(n), num, buffer.data());
  if (e == nullptr)
  {
    return nullptr;
  }
  return d_context.isRelevant(e) ? e : nullptr;
}

ENode* Checker::getENodeEqTo(TNode n)
{
  if (isVar(n))
  {
    uint32_t idx = varIndex(n);
    if (idx >= d_numBindings)
    {
      return nullptr;
    }
    return d_bindings[idx];
  }
  if (d_context.eInternalized(n) && d_context.isRelevant(n))
  {
    return d_context.getENode(n);
  }
  if (!isApp(n) || n.getNumChildren() == 0)
  {
    return nullptr;
  }
  auto it = d_toENodeCache.find(n);
  if (it != d_toENodeCache.end())
  {
    return it->second;
  }
  ENode* r = getENodeEqToCore(n);
  d_toENodeCache[n] = r;
  return r;
}

bool Checker::isSat(TNode n, size_t numBindings, ENode* const* bindings)
{
  d_numBindings = numBindings;
  d_bindings = bindings;
  bool r = check(n, 0, true);
  d_isTrueCache[0].clear();
  d_isTrueCache[1].clear();
  d_toENodeCache.clear();
  d_numBindings = 0;
  d_bindings = nullptr;
  return r;
}

bool Checker::isUnsat(TNode n, size_t numBindings, ENode* const* bindings)
{
  d_numBindings = numBindings;
  d_bindings = bindings;
  bool r = check(n, 0, false);
  d_isTrueCache[0].clear();
  d_isTrueCache[1].clear();
  d_toENodeCache.clear();
  d_numBindings = 0;
  d_bindings = nullptr;
  return r;
}

}  // namespace z3
}  // namespace cvc5::internal
