/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An association list from theory id to theory variable, stored inline in the
 * enode and extended with region-allocated cells.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/util/id_var_list.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__ID_VAR_LIST_H
#define CVC5__Z3__UTIL__ID_VAR_LIST_H

#include "base/check.h"
#include "z3/util/region.h"

namespace cvc5::internal {
namespace z3 {

/**
 * A singly linked association list from an id in [0..255] to a 24-bit
 * variable. The first cell is stored inline in its owner (an enode), so the
 * common case of a node that no theory, or exactly one theory, cares about
 * costs no extra allocation.
 */
template <int nullId = -1, int nullVar = -1>
class IdVarList
{
 public:
  IdVarList() : d_id(nullId), d_var(nullVar), d_next(nullptr) {}

  IdVarList(int t, int v, IdVarList* n = nullptr)
      : d_id(t), d_var(v), d_next(n)
  {
  }

  int getId() const { return d_id; }

  int getVar() const { return d_var; }

  bool empty() const { return getVar() == nullVar; }

  /** Return the variable associated with id, or nullVar. */
  int find(int id) const
  {
    if (empty())
    {
      return nullVar;
    }
    const IdVarList* l = this;
    do
    {
      if (id == l->getId())
      {
        return l->getVar();
      }
      l = l->getNext();
    } while (l != nullptr);
    return nullVar;
  }

  size_t size() const
  {
    if (empty())
    {
      return 0;
    }
    size_t r = 0;
    const IdVarList* l = this;
    while (l != nullptr)
    {
      ++r;
      l = l->getNext();
    }
    return r;
  }

  /** Associate v with id, allocating a new cell in r if needed. */
  void addVar(int v, int id, Region& r)
  {
    Assert(find(id) == nullVar);
    if (getVar() == nullVar)
    {
      d_var = v;
      d_id = id;
      d_next = nullptr;
    }
    else
    {
      IdVarList* l = this;
      while (l->getNext() != nullptr)
      {
        Assert(l->getId() != id);
        l = l->getNext();
      }
      Assert(l != nullptr);
      Assert(l->getNext() == nullptr);
      IdVarList<nullId, nullVar>* newCell =
          new (r) IdVarList<nullId, nullVar>(id, v);
      l->setNext(newCell);
    }
    Assert(find(id) == v);
  }

  /**
   * Replace the entry (v', id) with the entry (v, id). There must already be
   * an entry for id.
   */
  void replace(int v, int id)
  {
    Assert(find(id) != nullVar);
    IdVarList* l = this;
    while (l != nullptr)
    {
      if (l->getId() == id)
      {
        l->setVar(v);
        return;
      }
      l = l->getNext();
    }
    Unreachable();
  }

  /**
   * Delete the theory variable for id. There must already be an entry for id.
   */
  void delVar(int id)
  {
    Assert(find(id) != nullVar);
    if (getId() == id)
    {
      if (d_next == nullptr)
      {
        // most common case
        d_var = nullVar;
        d_id = nullId;
      }
      else
      {
        d_var = d_next->getVar();
        d_id = d_next->getId();
        d_next = d_next->getNext();
      }
    }
    else
    {
      IdVarList* prev = this;
      IdVarList* l = prev->getNext();
      while (l != nullptr)
      {
        Assert(prev->getNext() == l);
        if (l->getId() == id)
        {
          prev->setNext(l->getNext());
          return;
        }
        prev = l;
        l = l->getNext();
      }
      Unreachable();
    }
  }

  IdVarList* getNext() const { return d_next; }

  void setId(int id) { d_id = id; }

  void setVar(int v) { d_var = v; }

  void setNext(IdVarList* next) { d_next = next; }

 private:
  int d_id : 8;
  int d_var : 24;
  IdVarList* d_next;
};

static_assert(sizeof(unsigned*) != 8
                  || sizeof(IdVarList<>)
                         == sizeof(IdVarList<>*) + sizeof(int)
                                + /* alignment padding */ sizeof(int),
              "unexpected IdVarList layout on a 64 bit machine");

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__ID_VAR_LIST_H */
