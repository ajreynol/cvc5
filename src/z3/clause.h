/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Clauses of the ported Z3 SMT core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_clause.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__CLAUSE_H
#define CVC5__Z3__CLAUSE_H

#include <new>
#include <ostream>
#include <vector>

#include "expr/node.h"
#include "z3/util/literal.h"

namespace cvc5::internal {
namespace z3 {

class Clause;
class Justification;

/** An event handler invoked when a clause is deleted. */
class ClauseDelEh
{
 public:
  virtual ~ClauseDelEh() = default;
  virtual void operator()(Clause* cls) = 0;
};

enum ClauseKind
{
  /** an input assumption */
  CLS_AUX,
  /** a theory axiom */
  CLS_TH_AXIOM,
  /** learned through conflict resolution */
  CLS_LEARNED,
  /** a theory lemma */
  CLS_TH_LEMMA
};

inline bool isAxiom(ClauseKind k)
{
  return k == CLS_AUX || k == CLS_TH_AXIOM;
}

inline bool isLemma(ClauseKind k)
{
  return k == CLS_LEARNED || k == CLS_TH_LEMMA;
}

/**
 * A clause of the ported Z3 core.
 *
 * As in Z3, the literals are stored inline immediately after the header and
 * the optional fields are appended after them, so that a clause costs one
 * allocation and its literals are contiguous. The optional fields are an
 * activity counter (for lemmas), a deletion handler, a justification, and the
 * atoms needed to re-internalize the clause after backtracking.
 *
 * Z3 stores each saved atom as an expr* with the literal's sign packed into
 * the low pointer bit. Here an atom is a cvc5 Node together with its sign,
 * which costs a word more per saved atom but lets the reference counting be
 * the Node's own.
 */
class Clause
{
 public:
  /** A saved atom and the sign of the literal it came from. */
  struct AtomEntry
  {
    Node d_atom;
    bool d_sign;
  };

  /**
   * Create a new clause. boolVar2Expr maps a Boolean variable to its atom and
   * is only used when saveAtoms is true.
   */
  static Clause* mk(size_t numLits,
                    Literal* lits,
                    ClauseKind k,
                    Justification* js = nullptr,
                    ClauseDelEh* delEh = nullptr,
                    bool saveAtoms = false,
                    const std::vector<Node>* boolVar2Expr = nullptr);

  void deallocate();

  ClauseKind getKind() const { return static_cast<ClauseKind>(d_kind); }

  bool isLemma() const { return z3::isLemma(getKind()); }

  bool isLearned() const { return getKind() == CLS_LEARNED; }

  bool isThLemma() const { return getKind() == CLS_TH_LEMMA; }

  bool inReinitStack() const { return d_reinit; }

  bool reinternalizeAtoms() const { return d_reinternalizeAtoms; }

  size_t getNumLiterals() const { return d_numLiterals; }

  Literal& operator[](size_t idx)
  {
    Assert(idx < d_numLiterals);
    return litsPtr()[idx];
  }

  Literal operator[](size_t idx) const
  {
    Assert(idx < d_numLiterals);
    return litsPtr()[idx];
  }

  Literal getLiteral(size_t idx) const { return (*this)[idx]; }

  Literal& getLiteral(size_t idx) { return (*this)[idx]; }

  Literal* begin() { return litsPtr(); }

  Literal* end() { return litsPtr() + d_numLiterals; }

  const Literal* begin() const { return litsPtr(); }

  const Literal* end() const { return litsPtr() + d_numLiterals; }

  uint32_t getActivity() const
  {
    Assert(isLemma());
    return *getActivityAddr();
  }

  void setActivity(uint32_t act)
  {
    Assert(isLemma());
    *getActivityAddr() = act;
  }

  void incClauseActivity()
  {
    Assert(isLemma());
    setActivity(getActivity() + 1);
  }

  ClauseDelEh* getDelEh() const
  {
    return d_hasDelEh ? *getDelEhAddr() : nullptr;
  }

  Justification* getJustification() const
  {
    return d_hasJustification ? *getJustificationAddr() : nullptr;
  }

  size_t getNumAtoms() const { return d_reinternalizeAtoms ? d_numLiterals : 0; }

  TNode getAtom(size_t idx) const
  {
    Assert(idx < getNumAtoms());
    return getAtomsAddr()[idx].d_atom;
  }

  bool getAtomSign(size_t idx) const
  {
    Assert(idx < getNumAtoms());
    return getAtomsAddr()[idx].d_sign;
  }

  size_t hash() const { return reinterpret_cast<size_t>(this) >> 3; }

  void markAsDeleted()
  {
    Assert(!d_deleted);
    d_deleted = true;
    ClauseDelEh* delEh = getDelEh();
    if (delEh != nullptr)
    {
      (*delEh)(this);
      *(const_cast<ClauseDelEh**>(getDelEhAddr())) = nullptr;
    }
  }

  bool deleted() const { return d_deleted; }

  std::ostream& print(std::ostream& out,
                      const std::vector<Node>& boolVar2Expr) const;

 private:
  uint32_t d_numLiterals;
  /**
   * Some of the clause literals may be simplified away; this field holds the
   * original number of literals, which is what the allocation size is based
   * on.
   */
  uint32_t d_capacity : 24;
  uint32_t d_kind : 2;
  /** true if the clause is in the reinit stack */
  uint32_t d_reinit : 1;
  /** true if the atoms must be re-internalized during reinitialization */
  uint32_t d_reinternalizeAtoms : 1;
  /** true if the clause has memory reserved for storing atoms */
  uint32_t d_hasAtoms : 1;
  /** true if a handler must be notified when the clause is deleted */
  uint32_t d_hasDelEh : 1;
  /** true if a justification is attached to the clause */
  uint32_t d_hasJustification : 1;
  /**
   * true if the clause is marked for deletion but was not deleted yet,
   * because it is still referenced from somewhere
   */
  uint32_t d_deleted : 1;

  static size_t getObjSize(size_t numLits,
                           ClauseKind k,
                           bool hasAtoms,
                           bool hasDelEh,
                           bool hasJustification)
  {
    size_t r = sizeof(Clause) + sizeof(Literal) * numLits;
    if (z3::isLemma(k))
    {
      r += sizeof(uint32_t);
    }
    r = align(r);
    if (hasDelEh)
    {
      r += sizeof(ClauseDelEh*);
    }
    if (hasJustification)
    {
      r += sizeof(Justification*);
    }
    if (hasAtoms)
    {
      r += sizeof(AtomEntry) * numLits;
    }
    return r;
  }

  /** Round up to a pointer boundary. */
  static constexpr size_t align(size_t r)
  {
    return (r + (sizeof(void*) - 1)) & ~(sizeof(void*) - 1);
  }

  Literal* litsPtr()
  {
    return reinterpret_cast<Literal*>(reinterpret_cast<char*>(this)
                                      + sizeof(Clause));
  }

  const Literal* litsPtr() const
  {
    return reinterpret_cast<const Literal*>(
        reinterpret_cast<const char*>(this) + sizeof(Clause));
  }

  const uint32_t* getActivityAddr() const
  {
    return reinterpret_cast<const uint32_t*>(litsPtr() + d_capacity);
  }

  uint32_t* getActivityAddr()
  {
    return reinterpret_cast<uint32_t*>(litsPtr() + d_capacity);
  }

  /** The address just past the literals and the activity counter. */
  const char* afterLitsAddr() const
  {
    const uint32_t* addr = getActivityAddr();
    if (isLemma())
    {
      addr++;
    }
    size_t asInt = reinterpret_cast<size_t>(addr);
    return reinterpret_cast<const char*>(align(asInt));
  }

  ClauseDelEh* const* getDelEhAddr() const
  {
    return reinterpret_cast<ClauseDelEh* const*>(afterLitsAddr());
  }

  Justification* const* getJustificationAddr() const
  {
    ClauseDelEh* const* addr = getDelEhAddr();
    if (d_hasDelEh)
    {
      addr++;
    }
    return reinterpret_cast<Justification* const*>(addr);
  }

  AtomEntry* getAtomsAddr() const
  {
    Justification* const* addr = getJustificationAddr();
    if (d_hasJustification)
    {
      addr++;
    }
    return reinterpret_cast<AtomEntry*>(
        const_cast<Justification**>(addr));
  }

  friend class SmtContext;

  void swapLits(size_t idx1, size_t idx2)
  {
    Assert(idx1 < d_numLiterals);
    Assert(idx2 < d_numLiterals);
    std::swap(litsPtr()[idx1], litsPtr()[idx2]);
  }

  bool isWatch(Literal l) const
  {
    return litsPtr()[0] == l || litsPtr()[1] == l;
  }

  void setLiteral(size_t idx, Literal l) { litsPtr()[idx] = l; }

  void setNumLiterals(size_t n)
  {
    Assert(!d_reinit);
    d_numLiterals = static_cast<uint32_t>(n);
  }

  void setJustification(Justification* newJs)
  {
    Assert(d_hasJustification);
    Assert(!d_reinit);
    Justification** jsAddr =
        const_cast<Justification**>(getJustificationAddr());
    *jsAddr = newJs;
  }

  /** Drop the references to the saved atoms. */
  void releaseAtoms();
};

using ClauseVector = std::vector<Clause*>;

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__CLAUSE_H */
