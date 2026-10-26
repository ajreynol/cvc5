/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Nodes of the E-graph.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_enode.cpp, and recast in cvc5 style.
 */

#include "z3/quantifiers/enode.h"

#include <cstring>
#include <new>

#include "util/hash.h"
#include "z3/quantifiers/smt_context.h"
#include "z3/util/trail.h"

namespace cvc5::internal {
namespace z3 {

ENode* ENode::init(void* mem,
                   const App2ENode& app2enode,
                   TNode owner,
                   uint32_t generation,
                   bool suppressArgs,
                   bool mergeTf,
                   uint32_t iscopeLvl,
                   bool cgcEnabled,
                   bool updateChildrenParent)
{
  Assert(owner.getType().isBoolean() || !mergeTf);
  ENode* n = new (mem) ENode();
  n->d_owner = owner;
  bool isApplication = z3::isApp(owner);
  n->d_decl = isApplication ? z3::getDecl(owner) : TNode::null();
  n->d_root = n;
  n->d_next = n;
  n->d_cg = nullptr;
  n->d_classSize = 1;
  n->d_generation = generation;
  n->d_numArgs = (suppressArgs || !isApplication)
                     ? 0
                     : static_cast<uint32_t>(owner.getNumChildren());
  n->d_mark = false;
  n->d_mark2 = false;
  n->d_interpreted = false;
  n->d_eq = owner.getKind() == Kind::EQUAL;
  n->d_commutative = n->d_numArgs == 2 && z3::isCommutative(owner);
  n->d_bool = owner.getType().isBoolean();
  n->d_mergeTf = mergeTf;
  n->d_cgcEnabled = cgcEnabled;
  n->d_iscopeLvl = iscopeLvl;
  n->d_lblHash = -1;
  uint32_t numArgs = n->d_numArgs;
  ENode** args = n->argsPtr();
  for (uint32_t i = 0; i < numArgs; ++i)
  {
    ENode* arg = app2enode[owner[i].getId()];
    Assert(arg != nullptr);
    args[i] = arg;
    if (updateChildrenParent)
    {
      arg->getRoot()->d_parents.push_back(n);
    }
  }
  return n;
}

ENode* ENode::mk(TrailStack& r,
                 const App2ENode& app2enode,
                 TNode owner,
                 uint32_t generation,
                 bool suppressArgs,
                 bool mergeTf,
                 uint32_t iscopeLvl,
                 bool cgcEnabled,
                 bool updateChildrenParent)
{
  Assert(owner.getType().isBoolean() || !mergeTf);
  size_t numArgs =
      (suppressArgs || !z3::isApp(owner)) ? 0 : owner.getNumChildren();
  size_t sz = getENodeSize(numArgs);
  void* mem = r.allocate(sz);
  return init(mem,
              app2enode,
              owner,
              generation,
              suppressArgs,
              mergeTf,
              iscopeLvl,
              cgcEnabled,
              updateChildrenParent);
}

ENode* ENode::mkDummy(const App2ENode& app2enode, TNode owner)
{
  size_t sz = getENodeSize(owner.getNumChildren());
  void* mem = ::operator new(sz);
  return init(mem, app2enode, owner, 0, false, false, 0, true, false);
}

void ENode::delEh(bool updateChildrenParent)
{
  Assert(d_classSize == 1);
  Assert(d_root == this);
  Assert(d_next == this);
  uint32_t numArgs = getNumArgs();
  for (uint32_t i = 0; i < numArgs; ++i)
  {
    ENode* arg = getArg(i);
    if (updateChildrenParent)
    {
      Assert(arg->getRoot()->d_parents.back() == this);
      arg->getRoot()->d_parents.pop_back();
    }
  }
  this->~ENode();
}

void ENode::setLblHash(TrailStack& trail)
{
  Assert(d_lblHash == -1);
  // d_lblHash is different from -1 if and only if there is a pattern that
  // contains this enode, so a trail restores it to -1.
  trail.push(ValueTrail<int8_t>(d_lblHash));
  uint64_t h = fnv1a::fnv1a_64(getOwnerId());
  d_lblHash = static_cast<int8_t>(h & (approxSetCapacity() - 1));
  // propagate the modification to the root's label set
  ApproxSet& rLbls = d_root->d_lbls;
  if (!rLbls.mayContain(static_cast<uint32_t>(d_lblHash)))
  {
    trail.push(ValueTrail<ApproxSet>(rLbls));
    rLbls.insert(static_cast<uint32_t>(d_lblHash));
  }
}

bool congruentApps(ENode* n1, ENode* n2)
{
  if (n1->getDecl() != n2->getDecl())
  {
    return false;
  }
  uint32_t numArgs = n1->getNumArgs();
  if (numArgs != n2->getNumArgs())
  {
    return false;
  }
  if (n1->isCommutative())
  {
    ENode* c11 = n1->getArg(0)->getRoot();
    ENode* c12 = n1->getArg(1)->getRoot();
    ENode* c21 = n2->getArg(0)->getRoot();
    ENode* c22 = n2->getArg(1)->getRoot();
    if (c11 == c21 && c12 == c22)
    {
      return true;
    }
    return c11 == c22 && c12 == c21;
  }
  for (uint32_t i = 0; i < numArgs; ++i)
  {
    if (n1->getArg(i)->getRoot() != n2->getArg(i)->getRoot())
    {
      return false;
    }
  }
  return true;
}

void unmarkENodes(size_t numENodes, ENode* const* enodes)
{
  for (size_t i = 0; i < numENodes; ++i)
  {
    enodes[i]->unsetMark();
  }
}

void unmarkENodes2(size_t numENodes, ENode* const* enodes)
{
  for (size_t i = 0; i < numENodes; ++i)
  {
    enodes[i]->unsetMark2();
  }
}

TmpENode::TmpENode() : d_capacity(0), d_enodeData(nullptr) { setCapacity(5); }

TmpENode::~TmpENode()
{
  if (d_enodeData != nullptr)
  {
    getENode()->~ENode();
    ::operator delete(d_enodeData);
  }
}

void TmpENode::setCapacity(size_t newCapacity)
{
  Assert(newCapacity > d_capacity);
  TNode decl;
  bool commutative = false;
  if (d_enodeData != nullptr)
  {
    decl = getENode()->d_decl;
    commutative = getENode()->d_commutative != 0;
    getENode()->~ENode();
    ::operator delete(d_enodeData);
  }
  d_capacity = newCapacity;
  size_t sz = ENode::getENodeSize(d_capacity);
  d_enodeData = static_cast<char*>(::operator new(sz));
  std::memset(d_enodeData, 0, sz);
  ENode* n = new (d_enodeData) ENode();
  n->d_root = n;
  n->d_next = n;
  n->d_classSize = 1;
  n->d_cgcEnabled = true;
  n->d_lblHash = -1;
  n->d_decl = decl;
  n->d_commutative = commutative;
}

ENode* TmpENode::set(TNode decl,
                     bool commutative,
                     size_t numArgs,
                     ENode* const* args)
{
  if (numArgs > d_capacity)
  {
    setCapacity(numArgs * 2);
  }
  ENode* r = getENode();
  if (r->d_decl != decl)
  {
    // the congruence table id is per declaration
    r->d_decl = decl;
  }
  r->d_numArgs = static_cast<uint32_t>(numArgs);
  r->d_commutative = numArgs == 2 && commutative;
  std::memcpy(r->argsPtr(), args, sizeof(ENode*) * numArgs);
  return r;
}

}  // namespace z3
}  // namespace cvc5::internal
