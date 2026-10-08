/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The congruence table.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_cg_table.cpp, and recast in cvc5 style.
 */

#include "z3/cg_table.h"

#include "expr/node_manager.h"

namespace cvc5::internal {
namespace z3 {

size_t CgTable::CgHash::operator()(ENode* n) const
{
  uint32_t a, b, c;
  a = b = 0x9e3779b9;
  c = 11;

  uint32_t i = n->getNumArgs();
  while (i >= 3)
  {
    i--;
    a += static_cast<uint32_t>(n->getArg(i)->getRoot()->hash());
    i--;
    b += static_cast<uint32_t>(n->getArg(i)->getRoot()->hash());
    i--;
    c += static_cast<uint32_t>(n->getArg(i)->getRoot()->hash());
    hashMix(a, b, c);
  }

  switch (i)
  {
    case 2:
      b += static_cast<uint32_t>(n->getArg(1)->getRoot()->hash());
      CVC5_FALLTHROUGH;
    case 1: c += static_cast<uint32_t>(n->getArg(0)->getRoot()->hash());
  }
  hashMix(a, b, c);
  return c;
}

bool CgTable::CgEq::operator()(ENode* n1, ENode* n2) const
{
  Assert(n1->getDecl() == n2->getDecl());
  uint32_t num = n1->getNumArgs();
  if (num != n2->getNumArgs())
  {
    return false;
  }
  for (uint32_t i = 0; i < num; ++i)
  {
    if (n1->getArg(i)->getRoot() != n2->getArg(i)->getRoot())
    {
      return false;
    }
  }
  return true;
}

CgTable::CgTable() : d_commutativity(false) {}

CgTable::~CgTable() { reset(); }

CgTable::Table CgTable::mkTableFor(ENode* n)
{
  Assert(n->getNumArgs() >= 1);
  // Applications of n-ary operators (e.g. +) may have many arguments, so they
  // always go to the general table even when this particular application is
  // unary or binary. This is Z3's is_flat_associative() test.
  if (NodeManager::isNAryKind(n->getExpr().getKind()))
  {
    return Table{NARY, new NaryTable()};
  }
  switch (n->getNumArgs())
  {
    case 1: return Table{UNARY, new UnaryTable()};
    case 2:
      if (n->isCommutative())
      {
        return Table{
            BINARY_COMM,
            new CommTable(0, CgCommHash(), CgCommEq(&d_commutativity))};
      }
      return Table{BINARY, new BinaryTable()};
    default: return Table{NARY, new NaryTable()};
  }
}

uint32_t CgTable::setFuncDeclId(ENode* n)
{
  TNode f = n->getDecl();
  uint32_t tid;
  auto it = d_funcDecl2Id.find(f);
  if (it == d_funcDecl2Id.end())
  {
    tid = static_cast<uint32_t>(d_tables.size());
    d_funcDecl2Id[f] = tid;
    d_tables.push_back(mkTableFor(n));
  }
  else
  {
    tid = it->second;
  }
  Assert(tid < d_tables.size());
  n->setFuncDeclId(tid);
  return tid;
}

void CgTable::reset()
{
  for (const Table& t : d_tables)
  {
    switch (t.d_kind)
    {
      case UNARY: delete static_cast<UnaryTable*>(t.d_table); break;
      case BINARY: delete static_cast<BinaryTable*>(t.d_table); break;
      case BINARY_COMM: delete static_cast<CommTable*>(t.d_table); break;
      case NARY: delete static_cast<NaryTable*>(t.d_table); break;
    }
  }
  d_tables.clear();
  d_funcDecl2Id.clear();
}

ENodeBoolPair CgTable::insert(ENode* n)
{
  // it does not make sense to insert a constant
  Assert(n->getNumArgs() > 0);
  Table t = getTable(n);
  switch (t.d_kind)
  {
    case UNARY:
    {
      auto r = static_cast<UnaryTable*>(t.d_table)->insert(n);
      return ENodeBoolPair(*r.first, false);
    }
    case BINARY:
    {
      auto r = static_cast<BinaryTable*>(t.d_table)->insert(n);
      return ENodeBoolPair(*r.first, false);
    }
    case BINARY_COMM:
    {
      d_commutativity = false;
      auto r = static_cast<CommTable*>(t.d_table)->insert(n);
      return ENodeBoolPair(*r.first, d_commutativity);
    }
    default:
    {
      auto r = static_cast<NaryTable*>(t.d_table)->insert(n);
      return ENodeBoolPair(*r.first, false);
    }
  }
}

void CgTable::erase(ENode* n)
{
  Assert(n->getNumArgs() > 0);
  Table t = getTable(n);
  switch (t.d_kind)
  {
    case UNARY: static_cast<UnaryTable*>(t.d_table)->erase(n); break;
    case BINARY: static_cast<BinaryTable*>(t.d_table)->erase(n); break;
    case BINARY_COMM: static_cast<CommTable*>(t.d_table)->erase(n); break;
    default: static_cast<NaryTable*>(t.d_table)->erase(n); break;
  }
}

bool CgTable::contains(ENode* n) const
{
  Assert(n->getNumArgs() > 0);
  Table t = getTable(n);
  switch (t.d_kind)
  {
    case UNARY:
    {
      const UnaryTable* tb = static_cast<const UnaryTable*>(t.d_table);
      return tb->find(n) != tb->end();
    }
    case BINARY:
    {
      const BinaryTable* tb = static_cast<const BinaryTable*>(t.d_table);
      return tb->find(n) != tb->end();
    }
    case BINARY_COMM:
    {
      const CommTable* tb = static_cast<const CommTable*>(t.d_table);
      return tb->find(n) != tb->end();
    }
    default:
    {
      const NaryTable* tb = static_cast<const NaryTable*>(t.d_table);
      return tb->find(n) != tb->end();
    }
  }
}

ENode* CgTable::find(ENode* n) const
{
  Assert(n->getNumArgs() > 0);
  Table t = getTable(n);
  switch (t.d_kind)
  {
    case UNARY:
    {
      const UnaryTable* tb = static_cast<const UnaryTable*>(t.d_table);
      auto it = tb->find(n);
      return it == tb->end() ? nullptr : *it;
    }
    case BINARY:
    {
      const BinaryTable* tb = static_cast<const BinaryTable*>(t.d_table);
      auto it = tb->find(n);
      return it == tb->end() ? nullptr : *it;
    }
    case BINARY_COMM:
    {
      const CommTable* tb = static_cast<const CommTable*>(t.d_table);
      auto it = tb->find(n);
      return it == tb->end() ? nullptr : *it;
    }
    default:
    {
      const NaryTable* tb = static_cast<const NaryTable*>(t.d_table);
      auto it = tb->find(n);
      return it == tb->end() ? nullptr : *it;
    }
  }
}

bool CgTable::containsPtr(ENode* n) const
{
  ENode* r = find(n);
  return r == n;
}

void CgTable::print(std::ostream& out) const
{
  for (const std::pair<const TNode, uint32_t>& kv : d_funcDecl2Id)
  {
    Table t = d_tables[kv.second];
    out << kv.first << ": ";
    switch (t.d_kind)
    {
      case UNARY:
        out << "un ";
        for (ENode* n : *static_cast<const UnaryTable*>(t.d_table))
        {
          out << n->getOwnerId() << " ";
        }
        break;
      case BINARY:
        out << "b ";
        for (ENode* n : *static_cast<const BinaryTable*>(t.d_table))
        {
          out << n->getOwnerId() << " ";
        }
        break;
      case BINARY_COMM:
        out << "bc ";
        for (ENode* n : *static_cast<const CommTable*>(t.d_table))
        {
          out << n->getOwnerId() << " ";
        }
        break;
      case NARY:
        out << "nary ";
        for (ENode* n : *static_cast<const NaryTable*>(t.d_table))
        {
          out << n->getOwnerId() << " ";
        }
        break;
    }
    out << "\n";
  }
}

bool CgTable::checkInvariant() const
{
#ifdef CVC5_ASSERTIONS
  for (const Table& t : d_tables)
  {
    switch (t.d_kind)
    {
      case UNARY:
        for (ENode* n : *static_cast<const UnaryTable*>(t.d_table))
        {
          Assert(n->isCgr());
        }
        break;
      case BINARY:
        for (ENode* n : *static_cast<const BinaryTable*>(t.d_table))
        {
          Assert(n->isCgr());
        }
        break;
      case BINARY_COMM:
        for (ENode* n : *static_cast<const CommTable*>(t.d_table))
        {
          Assert(n->isCgr());
        }
        break;
      case NARY:
        for (ENode* n : *static_cast<const NaryTable*>(t.d_table))
        {
          Assert(n->isCgr());
        }
        break;
    }
  }
#endif
  return true;
}

}  // namespace z3
}  // namespace cvc5::internal
