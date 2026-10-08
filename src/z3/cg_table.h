/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The congruence table: one hash table per function symbol, keyed on the
 * equivalence class roots of the arguments.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_cg_table.h, and recast in cvc5 style.
 *
 * Note Z3 backs these tables with its own open-addressing chashtable, while
 * this port uses std::unordered_set, which chains and allocates a node per
 * element. The table is hot in E-matching-heavy problems, so this is a place
 * to revisit if profiling shows it matters.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__CG_TABLE_H
#define CVC5__Z3__CG_TABLE_H

#include <unordered_map>
#include <unordered_set>

#include "z3/enode.h"
#include "z3/util/hash.h"

namespace cvc5::internal {
namespace z3 {

using ENodeBoolPair = std::pair<ENode*, bool>;

/**
 * The congruence table.
 *
 * Congruence is keyed on the declaration and the equivalence class roots of
 * the arguments. Since the declaration fixes the arity, the table is split per
 * declaration and specialized by arity, which is what makes the common unary
 * and binary cases cheap. The binary commutative case treats the two arguments
 * as unordered and reports back whether a match used commutativity.
 */
class CgTable
{
  struct CgUnaryHash
  {
    size_t operator()(ENode* n) const
    {
      Assert(n->getNumArgs() == 1);
      return n->getArg(0)->getRoot()->hash();
    }
  };

  struct CgUnaryEq
  {
    bool operator()(ENode* n1, ENode* n2) const
    {
      Assert(n1->getNumArgs() == 1);
      Assert(n2->getNumArgs() == 1);
      Assert(n1->getDecl() == n2->getDecl());
      return n1->getArg(0)->getRoot() == n2->getArg(0)->getRoot();
    }
  };

  using UnaryTable = std::unordered_set<ENode*, CgUnaryHash, CgUnaryEq>;

  struct CgBinaryHash
  {
    size_t operator()(ENode* n) const
    {
      Assert(n->getNumArgs() == 2);
      return combineHash(
          static_cast<uint32_t>(n->getArg(0)->getRoot()->hash()),
          static_cast<uint32_t>(n->getArg(1)->getRoot()->hash()));
    }
  };

  struct CgBinaryEq
  {
    bool operator()(ENode* n1, ENode* n2) const
    {
      Assert(n1->getNumArgs() == 2);
      Assert(n2->getNumArgs() == 2);
      Assert(n1->getDecl() == n2->getDecl());
      return n1->getArg(0)->getRoot() == n2->getArg(0)->getRoot()
             && n1->getArg(1)->getRoot() == n2->getArg(1)->getRoot();
    }
  };

  using BinaryTable = std::unordered_set<ENode*, CgBinaryHash, CgBinaryEq>;

  struct CgCommHash
  {
    size_t operator()(ENode* n) const
    {
      Assert(n->getNumArgs() == 2);
      uint32_t h1 = static_cast<uint32_t>(n->getArg(0)->getRoot()->hash());
      uint32_t h2 = static_cast<uint32_t>(n->getArg(1)->getRoot()->hash());
      if (h1 > h2)
      {
        std::swap(h1, h2);
      }
      return hashU((h1 << 16) | (h2 & 0xFFFF));
    }
  };

  struct CgCommEq
  {
    bool* d_commutativity;
    CgCommEq(bool* c) : d_commutativity(c) {}
    bool operator()(ENode* n1, ENode* n2) const
    {
      Assert(n1->getNumArgs() == 2);
      Assert(n2->getNumArgs() == 2);
      Assert(n1->getDecl() == n2->getDecl());
      ENode* c11 = n1->getArg(0)->getRoot();
      ENode* c12 = n1->getArg(1)->getRoot();
      ENode* c21 = n2->getArg(0)->getRoot();
      ENode* c22 = n2->getArg(1)->getRoot();
      if (c11 == c21 && c12 == c22)
      {
        return true;
      }
      if (c11 == c22 && c12 == c21)
      {
        *d_commutativity = true;
        return true;
      }
      return false;
    }
  };

  using CommTable = std::unordered_set<ENode*, CgCommHash, CgCommEq>;

  struct CgHash
  {
    size_t operator()(ENode* n) const;
  };

  struct CgEq
  {
    bool operator()(ENode* n1, ENode* n2) const;
  };

  using NaryTable = std::unordered_set<ENode*, CgHash, CgEq>;

  enum TableKind
  {
    UNARY,
    BINARY,
    BINARY_COMM,
    NARY
  };

  /** One of the four table specializations, tagged by its kind. */
  struct Table
  {
    TableKind d_kind;
    void* d_table;
  };

 public:
  CgTable();
  ~CgTable();

  CgTable(const CgTable&) = delete;
  CgTable& operator=(const CgTable&) = delete;

  /**
   * Try to insert n. If the table already contains an element n' congruent to
   * n then nothing is inserted and (n', c) is returned, where c says whether n
   * and n' are congruent only modulo commutativity. Otherwise n is inserted
   * and (n, false) is returned.
   */
  ENodeBoolPair insert(ENode* n);

  void erase(ENode* n);

  bool contains(ENode* n) const;

  /** The element congruent to n, or null. */
  ENode* find(ENode* n) const;

  /** True if n itself is the element of the table congruent to n. */
  bool containsPtr(ENode* n) const;

  void reset();

  void print(std::ostream& out) const;

  bool checkInvariant() const;

 private:
  Table mkTableFor(ENode* n);
  uint32_t setFuncDeclId(ENode* n);

  Table getTable(ENode* n)
  {
    uint32_t tid = n->getFuncDeclId();
    if (tid == UINT32_MAX)
    {
      tid = setFuncDeclId(n);
    }
    Assert(tid < d_tables.size());
    return d_tables[tid];
  }

  Table getTable(ENode* n) const
  {
    return const_cast<CgTable*>(this)->getTable(n);
  }

  /** True if the last found congruence used commutativity. */
  bool d_commutativity;
  std::vector<Table> d_tables;
  std::unordered_map<TNode, uint32_t> d_funcDecl2Id;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__CG_TABLE_H */
