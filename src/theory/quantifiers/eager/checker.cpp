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
 * Ported from Z3: src/smt/smt_checker.cpp.
 * Z3 is Copyright (c) Microsoft Corporation and licensed under the MIT
 * License, see licenses/z3-LICENSE.
 */

#include "theory/quantifiers/eager/checker.h"

#include <vector>

#include "theory/quantifiers/eager/enode.h"
#include "theory/quantifiers/eager/egraph.h"
#include "theory/quantifiers/eager/prop_core.h"
#include "theory/quantifiers/eager/quantifier_normalizer.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

namespace {

/** The depth at which the structural evaluation gives up. */
constexpr size_t s_maxDepth = 600;
}  // namespace

Checker::Checker(EGraph& egraph, PropCore& prop)
    : d_egraph(egraph),
      d_prop(prop),
      d_numBindings(0),
      d_bindings(nullptr)
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
  if (d_prop.bInternalized(n)
      && d_prop.isRelevant(n))
  {
    SatValue val = d_prop.getAssignment(n);
    return val != SAT_VALUE_UNKNOWN && isTrue == (val == SAT_VALUE_TRUE);
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
        if (lhs != nullptr && rhs != nullptr
            && d_prop.isRelevant(lhs->getExpr())
            && d_prop.isRelevant(rhs->getExpr()))
        {
          if (isTrue && lhs->getRoot() == rhs->getRoot())
          {
            return true;
          }
          if (!isTrue && isDiseq(lhs, rhs))
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
      if (d_prop.litInternalized(n[0])
          && d_prop.isRelevant(n[0]))
      {
        switch (d_prop.getAssignment(n[0]))
        {
          case SAT_VALUE_FALSE: return check(n[2], depth + 1, isTrue);
          case SAT_VALUE_UNKNOWN: return false;
          case SAT_VALUE_TRUE: return check(n[1], depth + 1, isTrue);
        }
      }
      return check(n[1], depth + 1, isTrue) && check(n[2], depth + 1, isTrue);
    }
    default: break;
  }
  ENode* e = getENodeEqTo(n);
  if (e != nullptr && e->isBool()
      && d_prop.isRelevant(e->getExpr()))
  {
    SatValue val = d_prop.getAssignment(e->getExpr());
    return val != SAT_VALUE_UNKNOWN && isTrue == (val == SAT_VALUE_TRUE);
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
      d_egraph.getENodeEqTo(getDecl(n), isCommutative(n), num, buffer.data());
  if (e == nullptr)
  {
    return nullptr;
  }
  return d_prop.isRelevant(e->getExpr()) ? e : nullptr;
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
  if (d_egraph.eInternalized(n) && d_prop.isRelevant(n))
  {
    return d_egraph.getENode(n);
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
  return run(n, numBindings, bindings, true);
}

bool Checker::isUnsat(TNode n, size_t numBindings, ENode* const* bindings)
{
  return run(n, numBindings, bindings, false);
}

bool Checker::run(TNode n,
                  size_t numBindings,
                  ENode* const* bindings,
                  bool isTrue)
{
  d_numBindings = numBindings;
  d_bindings = bindings;
  bool r = check(n, 0, isTrue);
  d_isTrueCache[0].clear();
  d_isTrueCache[1].clear();
  d_toENodeCache.clear();
  d_numBindings = 0;
  d_bindings = nullptr;
  return r;
}

bool Checker::isDiseq(ENode* n1, ENode* n2)
{
#ifdef CVC5_ASSERTIONS
  TypeNode sort1 = n1->getSort();
  TypeNode sort2 = n2->getSort();
  Assert(sort1 == sort2);
#endif
  TNode e1 = n1->getRoot()->getExpr();
  TNode e2 = n2->getRoot()->getExpr();
  if (e1.isConst() && e2.isConst() && e1 != e2)
  {
    return true;
  }
  // the equality of n1 and n2, if the E-graph has one
  Assert(NodeManager::hasOperator(Kind::EQUAL));
  ENode* args[2] = {n1, n2};
  ENode* r = d_egraph.getENodeEqTo(
      e1.getNodeManager()->operatorOf(Kind::EQUAL), true, 2, args);
  if (r != nullptr)
  {
    Assert(r->isEq());
    // the literal of the root of r, which is the false literal for false
    TNode re = r->getRoot()->getExpr();
    Assert(re.getType().isBoolean());
    SatLiteral l = (re.isConst() && !re.getConst<bool>())
                       ? s_falseLiteral
                       : SatLiteral(d_prop.getBoolVarOfId(re.getId()));
    return l != s_trueLiteral
           && (l == s_falseLiteral
               || (d_prop.isRelevant(l)
                   && d_prop.getAssignment(l) == SAT_VALUE_FALSE));
  }
  return false;
}

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal
