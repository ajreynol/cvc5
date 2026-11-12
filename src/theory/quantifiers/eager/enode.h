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
 * Ported from Z3: src/smt/smt_enode.h.
 * Z3 is Copyright (c) Microsoft Corporation and licensed under the MIT
 * License, see licenses/z3-LICENSE.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__ENODE_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__ENODE_H

#include <climits>
#include <cstdint>
#include <vector>

#include "expr/node.h"
#include "theory/quantifiers/eager/quantifier_normalizer.h"
#include "theory/quantifiers/eager/trail.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

class ENode;
class SmtContext;
class TrailStack;

using ENodeVector = std::vector<ENode*>;

/** Maps the id of a term to its enode. */
using App2ENode = std::vector<ENode*>;

/**
 * The congruence key of n: the node that stands in for Z3's func_decl*. For
 * parameterized kinds this is the operator, for kinds with a built-in operator
 * it is that operator, and for leaves it is n itself (a leaf is congruent to
 * nothing but itself).
 */
TNode getDecl(TNode n);

/**
 * True if n is a binary application of a commutative operator, in which case
 * the congruence table normalizes the argument order.
 */
bool isCommutative(TNode n);

// The label sets of the enodes, ported from Z3's src/util/approx_set.h.

/** The number of distinct bits available in an ApproxSet. */
constexpr uint32_t approxSetCapacity() { return 64; }

/**
 * A set of unsigned indices, approximated by a 64-bit mask: each index is
 * mapped to the bit at that index modulo 64.
 *
 * Membership is one-sided: mayContain() can return a false positive, but
 * a negative answer is exact. The same holds for the intersection test, which
 * is where the cheap filtering comes from. This is the variant used for enode
 * label sets, with an iterator over the bits that are set.
 */
class ApproxSet
{
 public:
  ApproxSet() = default;
  /** The singleton set {e}. */
  ApproxSet(uint32_t e) : d_set(toSet(e)) {}

  /** Add e to the set. */
  void insert(uint32_t e) { d_set |= toSet(e); }

  /** False only if e is definitely not in the set. */
  bool mayContain(uint32_t e) const { return (d_set & toSet(e)) != 0; }

  /** Add the elements of other to this set. */
  void operator|=(const ApproxSet& other) { d_set |= other.d_set; }

  /** True if no bit is set. */
  bool empty() const { return d_set == 0; }

  /** True if this set and other definitely share no element. */
  bool emptyIntersection(const ApproxSet& other) const
  {
    return (d_set & other.d_set) == 0;
  }

  /** Iterator over the indices of the set bits, in increasing order. */
  class iterator
  {
    /** The bits not yet visited, shifted so that bit 0 stands for d_val. */
    uint64_t d_set;
    /** The index the iterator is at. */
    uint32_t d_val;

    /** Advance to the lowest set bit at or after d_val, if any. */
    void moveToNext()
    {
      if (d_set > 0)
      {
        // after the shift the least significant bit is set
        uint32_t tz = static_cast<uint32_t>(__builtin_ctzll(d_set));
        d_val += tz;
        d_set >>= tz;
      }
    }

   public:
    /** An iterator at the lowest set bit of s; s == 0 gives end(). */
    iterator(uint64_t s) : d_set(s), d_val(0) { moveToNext(); }

    /** The index the iterator is at. */
    uint32_t operator*() const { return d_val; }

    /** Advance to the next set bit. */
    iterator& operator++()
    {
      d_val++;
      d_set >>= 1;
      moveToNext();
      return *this;
    }

    /** True if the iterators have different remaining bits. */
    bool operator!=(const iterator& it) const { return d_set != it.d_set; }
  };

  /** An iterator at the smallest element. */
  iterator begin() const { return iterator(d_set); }

  /** The past-the-end iterator. */
  static iterator end() { return iterator(0); }

  /** The number of bits set. */
  uint32_t size() const
  {
    return static_cast<uint32_t>(__builtin_popcountll(d_set));
  }

 private:
  /** The mask of u: the bit at index u modulo 64. */
  static uint64_t toSet(uint32_t u)
  {
    return UINT64_C(1) << (u & (approxSetCapacity() - 1));
  }

  /** The bit mask. */
  uint64_t d_set = 0;
};

class TmpENode;

/**
 * A node of the E-graph: the data structure implementing congruence closure,
 * equality propagation, and the central bus of equalities between theories.
 *
 * Enodes are allocated in the trail stack, with their argument array stored
 * inline directly after the fixed fields, and are released in bulk when the
 * scope they were created in is popped.
 */
class ENode
{
  /** The term that owns this enode. */
  TNode d_owner;
  /**
   * The congruence key of the owner: the node standing in for Z3's
   * func_decl*. Null if the owner is not an application.
   */
  TNode d_decl;
  /** The representative of the equivalence class. */
  ENode* d_root;
  /** The next element in the equivalence class, which is a circular list. */
  ENode* d_next;
  /** The congruence root this node was found congruent to. */
  ENode* d_cg;
  /** The size of the equivalence class, valid when this is the root. */
  uint32_t d_classSize;
  /**
   * The cached generation of the congruence class. Valid when isCgr(), or
   * when the enode does not use the congruence table (constants, leaves and
   * true-equality nodes), in which case it holds the enode's own generation.
   */
  uint32_t d_generation;
  /** The number of arguments stored inline after this object. */
  uint32_t d_numArgs;
  /** Multi-purpose auxiliary mark. */
  uint32_t d_mark : 1;
  /** Multi-purpose auxiliary mark. */
  uint32_t d_mark2 : 1;
  /** True if the node is an interpreted constant. */
  uint32_t d_interpreted : 1;
  /** True if the owner is an equality. */
  uint32_t d_eq : 1;
  /** True if the owner is a binary application of a commutative operator. */
  uint32_t d_commutative : 1;
  /** True if the owner is Boolean. */
  uint32_t d_bool : 1;
  /**
   * True if this node should be merged with true/false when the associated
   * Boolean variable is assigned.
   */
  uint32_t d_mergeTf : 1;
  /** True if congruence closure is enabled for this node. */
  uint32_t d_cgcEnabled : 1;
  /** The scope level at which this node was internalized. */
  uint32_t d_iscopeLvl;
  /** Different from -1 if this node is used in a pattern. */
  int8_t d_lblHash;

  /*
    The following property holds of d_parents:

    If this == d_root, then for every term f(a) such that a->getRoot() ==
    d_root, there is an f(b) in d_parents such that b->getRoot() == d_root,
    and f(a) and f(b) are congruent. Note f(a) and f(b) may have other
    arguments.

    Exception: if f(a) and f(b) are terms of the form (= a c) and (= b d),
    then d_parents will not contain (= b d) if b->getRoot() == d->getRoot().

    On relevancy propagation: relevancy is propagated to all elements of an
    equivalence class, so if some f(a) is relevant then the congruent f(b) in
    d_parents is relevant too.
  */
  /** The parent enodes of this equivalence class. */
  ENodeVector d_parents;
  /** Z3's lbls: approximates the labels of the class's terms; root only. */
  ApproxSet d_lbls;
  /** Z3's plbls: approximates the labels of the class's parents; root only. */
  ApproxSet d_plbls;

  friend class EGraph;
  friend class SmtContext;
  friend class QuantifierManager;
  friend class Mam;
  friend class TmpENode;
  friend class SetMergeTfTrail;

  /**
   * True if this node should be merged with the true (false) enode when the
   * associated Boolean variable is assigned to true (false).
   */
  bool mergeTf() const { return d_mergeTf; }

 public:
  /** Clear the merge-with-true/false flag; invoked from the trail. */
  void resetMergeTf() { d_mergeTf = false; }

 private:
  /** The inline argument array, stored directly after the fixed fields. */
  ENode** argsPtr()
  {
    return reinterpret_cast<ENode**>(reinterpret_cast<char*>(this)
                                     + sizeof(ENode));
  }

  /** The inline argument array, const version. */
  ENode* const* argsPtr() const
  {
    return reinterpret_cast<ENode* const*>(reinterpret_cast<const char*>(this)
                                           + sizeof(ENode));
  }

  /**
   * Construct the enode of owner in mem, which must have room for
   * getENodeSize of its arguments, and register it as a parent of the
   * classes of its arguments. If suppressArgs, the arguments of owner are
   * not recorded and the enode has none.
   */
  static ENode* init(void* mem,
                     const App2ENode& app2enode,
                     TNode owner,
                     uint32_t generation,
                     bool suppressArgs,
                     bool mergeTf,
                     uint32_t iscopeLvl,
                     bool cgcEnabled);

 public:
  /** The size in bytes of an enode with numArgs inline arguments. */
  static size_t getENodeSize(size_t numArgs)
  {
    return sizeof(ENode) + numArgs * sizeof(ENode*);
  }

  /** Allocate an enode for owner in the memory of trail stack r. */
  static ENode* mk(TrailStack& r,
                   const App2ENode& app2enode,
                   TNode owner,
                   uint32_t generation,
                   bool suppressArgs,
                   bool mergeTf,
                   uint32_t iscopeLvl,
                   bool cgcEnabled);

  /** Release this node, running its destructor. */
  void destroy();

  /** Mark this node, still a singleton class, as an interpreted constant. */
  void markAsInterpreted()
  {
    Assert(!d_interpreted);
    Assert(d_classSize == 1);
    d_interpreted = true;
  }

  /** The term that owns this enode. */
  TNode getExpr() const { return d_owner; }

  /** True if the owner is an application, leaves included; see eager::isApp. */
  bool isApp() const { return eager::isApp(d_owner); }

  /** The id of the owner. */
  uint32_t getOwnerId() const { return d_owner.getId(); }

  /** The congruence key, or a null node if the owner is not an application. */
  TNode getDecl() const { return d_decl; }

  /** The type of the owner. */
  TypeNode getSort() const { return d_owner.getType(); }

  /** The hash of this enode, which is the id of its owner. */
  size_t hash() const { return d_owner.getId(); }

  /** The representative of this node's equivalence class. */
  ENode* getRoot() const { return d_root; }

  /** The next member of this node's circular equivalence class list. */
  ENode* getNext() const { return d_next; }

  /** The number of arguments; 0 for leaves and suppressed arguments. */
  uint32_t getNumArgs() const { return d_numArgs; }

  /** The enode of the idx-th argument. */
  ENode* getArg(uint32_t idx) const
  {
    Assert(idx < getNumArgs());
    return argsPtr()[idx];
  }

  /** The argument array, of length getNumArgs(). */
  ENode* const* getArgs() const { return argsPtr(); }

  /** The size of the equivalence class, valid when this is the root. */
  uint32_t getClassSize() const { return d_classSize; }

  /** True if the owner is Boolean. */
  bool isBool() const { return d_bool; }

  /** True if the owner is an equality. */
  bool isEq() const { return d_eq; }

  /** True if this is an equality whose two sides are in the same class. */
  bool isTrueEq() const
  {
    return d_eq && getArg(0)->getRoot() == getArg(1)->getRoot();
  }

  /** True if the first auxiliary mark is set. */
  bool isMarked() const { return d_mark; }

  /** Set the first auxiliary mark, which must be unset. */
  void setMark()
  {
    Assert(!d_mark);
    d_mark = true;
  }

  /** Clear the first auxiliary mark, which must be set. */
  void unsetMark()
  {
    Assert(d_mark);
    d_mark = false;
  }

  /** True if the second auxiliary mark is set. */
  bool isMarked2() const { return d_mark2; }

  /** Set the second auxiliary mark, which must be unset. */
  void setMark2()
  {
    Assert(!d_mark2);
    d_mark2 = true;
  }

  /** Clear the second auxiliary mark, which must be set. */
  void unsetMark2()
  {
    Assert(d_mark2);
    d_mark2 = false;
  }

  /** True if the node is an interpreted constant. */
  bool isInterpreted() const { return d_interpreted; }

  /**
   * True if the node is not a constant and is the root of its congruence
   * class. Note that if getNumArgs() == 0 then isCgr() is false.
   */
  bool isCgr() const { return d_cg == this; }

  /** The congruence root this node was found congruent to (d_cg), or null. */
  ENode* getCg() const { return d_cg; }

  /**
   * True if this node is kept in the congruence table: it has arguments,
   * congruence closure is enabled for it, and it is not a true equality.
   */
  bool usesCgTable() const
  {
    return getNumArgs() > 0 && isCgcEnabled() && !isTrueEq();
  }

  /** True if congruence closure is enabled for this node. */
  bool isCgcEnabled() const { return d_cgcEnabled; }

  /** True if the owner is a binary application of a commutative operator. */
  bool isCommutative() const { return d_commutative; }

  /** The parents of this equivalence class. */
  const ENodeVector& getParents() const { return d_parents; }

  /** The number of parents of this equivalence class. */
  size_t getNumParents() const { return d_parents.size(); }

  /** A mutable iterator to the first parent. */
  ENodeVector::iterator beginParents() { return d_parents.begin(); }

  /** The mutable past-the-end iterator of the parents. */
  ENodeVector::iterator endParents() { return d_parents.end(); }

  /** Iterator over the members of the equivalence class. */
  class iterator
  {
    /** The member the iterator is at. */
    ENode* d_first;
    /** Null before the first increment, then the start of the iteration. */
    ENode* d_last;

   public:
    /** An iterator at n; m is null for begin() and n for end(). */
    iterator(ENode* n, ENode* m) : d_first(n), d_last(m) {}
    /** The member the iterator is at. */
    ENode* operator*() { return d_first; }
    /** Advance to the next member of the class. */
    iterator& operator++()
    {
      if (d_last == nullptr)
      {
        d_last = d_first;
      }
      d_first = d_first->d_next;
      return *this;
    }
    /** Postfix increment. */
    iterator operator++(int)
    {
      iterator tmp = *this;
      ++*this;
      return tmp;
    }
    /** True if the iterators are at different positions. */
    bool operator!=(const iterator& other) const
    {
      return d_last != other.d_last || d_first != other.d_first;
    }
  };

  /** An iterator at this node, the first member visited. */
  iterator begin() { return iterator(this, nullptr); }
  /** The iterator reached once every member has been visited. */
  iterator end() { return iterator(this, this); }

  /** The scope level at which this node was internalized. */
  uint32_t getIscopeLvl() const { return d_iscopeLvl; }

  /**
   * Give this node, which occurs as a ground subterm of a pattern, a label
   * hash derived from the id of its owner, and add it to the label set of
   * its root. Both changes are undone through trail.
   */
  void setLblHash(TrailStack& trail);

  /** True if setLblHash was called, i.e. the node occurs in a pattern. */
  bool hasLblHash() const { return d_lblHash >= 0; }

  /** The label hash, below approxSetCapacity(); see setLblHash. */
  uint8_t getLblHash() const
  {
    Assert(d_lblHash >= 0
           && static_cast<uint32_t>(d_lblHash) < approxSetCapacity());
    return static_cast<uint8_t>(d_lblHash);
  }

  /** The label set (Z3's lbls), meaningful at the root. */
  ApproxSet& getLbls() { return d_lbls; }

  /** The parent label set (Z3's plbls), meaningful at the root. */
  ApproxSet& getPlbls() { return d_plbls; }
};

/**
 * True if n1 and n2 have the same declaration and arguments in the same
 * equivalence classes, in either order if n1 is commutative. This is the
 * equality of the congruence table, where n1 or n2 may be a temporary enode
 * with no owner.
 */
bool congruentApps(ENode* n1, ENode* n2);

/** True if n1 and n2 are congruent applications. */
inline bool congruent(ENode* n1, ENode* n2)
{
  return n1->isApp() && congruentApps(n1, n2);
}

/** Clear the first auxiliary mark of each of the given enodes. */
void unmarkENodes(size_t numENodes, ENode* const* enodes);

/** Clear the second auxiliary mark of each of the given enodes. */
void unmarkENodes2(size_t numENodes, ENode* const* enodes);

/**
 * A reusable enode that is not part of the E-graph, used to look up whether a
 * congruent node already exists without creating one. Z3 fakes an application
 * for this; since cvc5 terms are hash-consed we instead set the congruence key
 * and argument count directly.
 */
class TmpENode
{
 public:
  /** Allocates room for a few arguments; set grows it on demand. */
  TmpENode();
  ~TmpENode();

  TmpENode(const TmpENode&) = delete;
  TmpENode& operator=(const TmpENode&) = delete;

  /** Configure this enode to stand for decl(args[0], ..., args[n-1]). */
  ENode* set(TNode decl, bool commutative, size_t numArgs, ENode* const* args);

 private:
  /** The enode stored in d_enodeData. */
  ENode* getENode() { return reinterpret_cast<ENode*>(d_enodeData); }
  /**
   * Reallocate the enode with room for newCapacity arguments, keeping its
   * congruence key and commutativity.
   */
  void setCapacity(size_t newCapacity);

  /** The number of arguments d_enodeData has room for. */
  size_t d_capacity;
  /** The memory of the enode, followed by its argument array. */
  char* d_enodeData;
};

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER__ENODE_H */
