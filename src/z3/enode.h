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
 * file src/smt/smt_enode.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__ENODE_H
#define CVC5__Z3__ENODE_H

#include <climits>
#include <vector>

#include "expr/node.h"
#include "z3/ast.h"
#include "z3/eq_justification.h"
#include "z3/types.h"
#include "z3/util/approx_set.h"
#include "z3/util/id_var_list.h"
#include "z3/util/region.h"

namespace cvc5::internal {
namespace z3 {

class SmtContext;

/** The justification for the transitivity rule. */
struct TransJustification
{
  ENode* d_target;
  EqJustification d_justification;
  TransJustification()
      : d_target(nullptr), d_justification(s_nullEqJustification)
  {
  }
};

/** Maps the id of a term to its enode. */
using App2ENode = std::vector<ENode*>;

using TheoryVarList = IdVarList<s_nullTheoryId, s_nullTheoryVar>;

class TmpENode;

/**
 * A node of the E-graph: the data structure implementing congruence closure,
 * equality propagation, and the central bus of equalities between theories.
 *
 * Enodes are allocated in a region, with their argument array stored inline
 * directly after the fixed fields, and are released in bulk when the scope
 * they were created in is popped.
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
  /** An id assigned by the congruence table, for fast table lookup. */
  uint32_t d_funcDeclId;
  /** The number of arguments stored inline after this object. */
  uint32_t d_numArgs;
  /** Multi-purpose auxiliary mark. */
  uint32_t d_mark : 1;
  /** Multi-purpose auxiliary mark. */
  uint32_t d_mark2 : 1;
  /** True if the node is an interpreted constant. */
  uint32_t d_interpreted : 1;
  /** True if the arguments of the owner should not be accessed. */
  uint32_t d_suppressArgs : 1;
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
  /** 0 - not shared, 1 - shared, 2 - invalid state. */
  uint32_t d_isShared : 2;
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
  /** The theories that care about this node. */
  TheoryVarList d_thVarList;
  /** A justification for this node being equal to its root. */
  TransJustification d_trans;
  ApproxSet d_lbls;
  ApproxSet d_plbls;

  friend class SmtContext;
  friend class ConflictResolution;
  friend class QuantifierManager;
  friend class Mam;
  friend class TmpENode;
  friend class SetMergeTfTrail;
  friend class AddThVarTrail;
  friend class ReplaceThVarTrail;

  TheoryVarList* getThVarListPtr()
  {
    return d_thVarList.getVar() == s_nullTheoryVar ? nullptr : &d_thVarList;
  }

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

  ENode* const* argsPtr() const
  {
    return reinterpret_cast<ENode* const*>(
        reinterpret_cast<const char*>(this) + sizeof(ENode));
  }

  static ENode* init(void* mem,
                     const App2ENode& app2enode,
                     TNode owner,
                     uint32_t generation,
                     bool suppressArgs,
                     bool mergeTf,
                     uint32_t iscopeLvl,
                     bool cgcEnabled,
                     bool updateChildrenParent);

 public:
  void addThVar(TheoryVar v, TheoryId id, Region& r);

  void replaceThVar(TheoryVar v, TheoryId id);

  void delThVar(TheoryId id);

  static size_t getENodeSize(size_t numArgs)
  {
    return sizeof(ENode) + numArgs * sizeof(ENode*);
  }

  /** Allocate an enode for owner in region r. */
  static ENode* mk(Region& r,
                   const App2ENode& app2enode,
                   TNode owner,
                   uint32_t generation,
                   bool suppressArgs,
                   bool mergeTf,
                   uint32_t iscopeLvl,
                   bool cgcEnabled,
                   bool updateChildrenParent);

  /** Allocate an enode outside any region, for temporary use. */
  static ENode* mkDummy(const App2ENode& app2enode, TNode owner);

  static void delDummy(ENode* n)
  {
    n->~ENode();
    ::operator delete(reinterpret_cast<char*>(n));
  }

  /** Release this node, running its destructor. */
  void delEh(bool updateChildrenParent = true);

  uint32_t getFuncDeclId() const { return d_funcDeclId; }

  void setFuncDeclId(uint32_t id) { d_funcDeclId = id; }

  void markAsInterpreted()
  {
    Assert(!d_interpreted);
    Assert(d_classSize == 1);
    d_interpreted = true;
  }

  TNode getExpr() const { return d_owner; }

  bool isApp() const { return z3::isApp(d_owner); }

  uint32_t getOwnerId() const { return d_owner.getId(); }

  uint32_t getExprId() const { return d_owner.getId(); }

  /** The congruence key, or a null node if the owner is not an application. */
  TNode getDecl() const { return d_decl; }

  TypeNode getSort() const { return d_owner.getType(); }

  TheoryId getFamilyId() const
  {
    return isApp() ? familyIdOf(d_owner) : theory::THEORY_BOOL;
  }

  size_t hash() const { return d_owner.getId(); }

  LBool isShared() const
  {
    switch (d_isShared)
    {
      case 0: return L_FALSE;
      case 1: return L_TRUE;
      default: return L_UNDEF;
    }
  }

  void setIsShared(LBool s)
  {
    switch (s)
    {
      case L_TRUE: d_isShared = 1; break;
      case L_FALSE: d_isShared = 0; break;
      default: d_isShared = 2; break;
    }
  }

  ENode* getRoot() const { return d_root; }

  bool isRoot() const { return d_root == this; }

  void setRoot(ENode* r) { d_root = r; }

  ENode* getNext() const { return d_next; }

  uint32_t getNumArgs() const { return d_numArgs; }

  ENode* getArg(uint32_t idx) const
  {
    Assert(idx < getNumArgs());
    return argsPtr()[idx];
  }

  ENode* const* getArgs() const { return argsPtr(); }

  /** Range over the arguments. */
  class ConstArgs
  {
    const ENode& d_n;

   public:
    ConstArgs(const ENode& n) : d_n(n) {}
    ConstArgs(const ENode* n) : d_n(*n) {}
    ENode* const* begin() const { return d_n.argsPtr(); }
    ENode* const* end() const { return d_n.argsPtr() + d_n.getNumArgs(); }
  };

  ConstArgs getConstArgs() const { return ConstArgs(this); }

  uint32_t getClassSize() const { return d_classSize; }

  bool isBool() const { return d_bool; }

  bool isEq() const { return d_eq; }

  bool isTrueEq() const
  {
    return d_eq && getArg(0)->getRoot() == getArg(1)->getRoot();
  }

  bool isMarked() const { return d_mark; }

  void setMark()
  {
    Assert(!d_mark);
    d_mark = true;
  }

  void unsetMark()
  {
    Assert(d_mark);
    d_mark = false;
  }

  bool isMarked2() const { return d_mark2; }

  void setMark2()
  {
    Assert(!d_mark2);
    d_mark2 = true;
  }

  void unsetMark2()
  {
    Assert(d_mark2);
    d_mark2 = false;
  }

  bool isInterpreted() const { return d_interpreted; }

  /**
   * True if the node is not a constant and is the root of its congruence
   * class. Note that if getNumArgs() == 0 then isCgr() is false.
   */
  bool isCgr() const { return d_cg == this; }

  ENode* getCg() const { return d_cg; }

  bool usesCgTable() const
  {
    return getNumArgs() > 0 && isCgcEnabled() && !isTrueEq();
  }

  bool isCgcEnabled() const { return d_cgcEnabled; }

  bool isCommutative() const { return d_commutative; }

  /** Range over the parents of this equivalence class. */
  class ConstParents
  {
    const ENode& d_n;

   public:
    ConstParents(const ENode& n) : d_n(n) {}
    ConstParents(const ENode* n) : d_n(*n) {}
    ENodeVector::const_iterator begin() const { return d_n.beginParents(); }
    ENodeVector::const_iterator end() const { return d_n.endParents(); }
  };

  class Parents
  {
    ENode& d_n;

   public:
    Parents(ENode& n) : d_n(n) {}
    Parents(ENode* n) : d_n(*n) {}
    ENodeVector::iterator begin() const { return d_n.beginParents(); }
    ENodeVector::iterator end() const { return d_n.endParents(); }
  };

  Parents getParents() { return Parents(this); }

  ConstParents getConstParents() const { return ConstParents(this); }

  size_t getNumParents() const { return d_parents.size(); }

  ENodeVector::iterator beginParents() { return d_parents.begin(); }

  ENodeVector::iterator endParents() { return d_parents.end(); }

  ENodeVector::const_iterator beginParents() const
  {
    return d_parents.begin();
  }

  ENodeVector::const_iterator endParents() const { return d_parents.end(); }

  /** Iterator over the members of the equivalence class. */
  class iterator
  {
    ENode* d_first;
    ENode* d_last;

   public:
    iterator(ENode* n, ENode* m) : d_first(n), d_last(m) {}
    ENode* operator*() { return d_first; }
    iterator& operator++()
    {
      if (d_last == nullptr)
      {
        d_last = d_first;
      }
      d_first = d_first->d_next;
      return *this;
    }
    iterator operator++(int)
    {
      iterator tmp = *this;
      ++*this;
      return tmp;
    }
    bool operator!=(const iterator& other) const
    {
      return d_last != other.d_last || d_first != other.d_first;
    }
  };

  iterator begin() { return iterator(this, nullptr); }
  iterator end() { return iterator(this, this); }

  const TheoryVarList* getThVarList() const
  {
    return d_thVarList.getVar() == s_nullTheoryVar ? nullptr : &d_thVarList;
  }

  bool hasThVars() const
  {
    return d_thVarList.getVar() != s_nullTheoryVar;
  }

  size_t getNumThVars() const;

  TheoryVar getThVar(TheoryId thId) const;

  TransJustification getTransJustification() { return d_trans; }

  /**
   * The enode in this equivalence class with the smallest generation.
   */
  ENode* getEqENodeWithMinGen(SmtContext* ctx);

  uint32_t getIscopeLvl() const { return d_iscopeLvl; }

  void setLblHash(SmtContext& ctx);

  bool hasLblHash() const { return d_lblHash >= 0; }

  uint8_t getLblHash() const
  {
    Assert(d_lblHash >= 0
           && static_cast<uint32_t>(d_lblHash) < approxSetCapacity());
    return static_cast<uint8_t>(d_lblHash);
  }

  ApproxSet& getLbls() { return d_lbls; }

  ApproxSet& getPlbls() { return d_plbls; }

  const ApproxSet& getLbls() const { return d_lbls; }

  const ApproxSet& getPlbls() const { return d_plbls; }

  void printLbls(std::ostream& out) const;
};

inline bool sameEqc(const ENode* n1, const ENode* n2)
{
  return n1->getRoot() == n2->getRoot();
}

/**
 * True if n1 and n2 are congruent. Sets comm to true if they are congruent
 * modulo commutativity.
 */
bool congruent(ENode* n1, ENode* n2, bool& comm);

inline bool congruent(ENode* n1, ENode* n2)
{
  bool aux;
  return congruent(n1, n2, aux);
}

void unmarkENodes(size_t numENodes, ENode* const* enodes);

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
  TmpENode();
  ~TmpENode();

  TmpENode(const TmpENode&) = delete;
  TmpENode& operator=(const TmpENode&) = delete;

  /** Configure this enode to stand for decl(args[0], ..., args[n-1]). */
  ENode* set(TNode decl, bool commutative, size_t numArgs, ENode* const* args);

  void reset();

 private:
  ENode* getENode() { return reinterpret_cast<ENode*>(d_enodeData); }
  void setCapacity(size_t newCapacity);

  size_t d_capacity;
  char* d_enodeData;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__ENODE_H */
