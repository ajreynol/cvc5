/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof-like objects for tracking dependencies in the ported Z3 SMT core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_justification.h, and recast in cvc5 style.
 *
 * Z3's justifications double as proof terms; this port drops proof production
 * (cvc5 produces proofs through its own machinery, which the Z3 core does not
 * feed), so only the dependency-tracking half is kept.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__JUSTIFICATION_H
#define CVC5__Z3__JUSTIFICATION_H

#include <vector>

#include "z3/eq_justification.h"
#include "z3/types.h"
#include "z3/util/literal.h"

namespace cvc5::internal {
namespace z3 {

class ConflictResolution;
class SmtContext;

using JustificationVector = std::vector<Justification*>;

/**
 * A pseudo-proof object, used to track dependencies.
 *
 * Justification objects follow a stack-based allocation policy, with one
 * exception: the justification of a lemma. A lemma created at scope level n may
 * outlive the backtracking of level n, since lemmas are only removed by the
 * periodic garbage collection. Justifications may therefore live either in a
 * region or on the heap, which inRegion() distinguishes.
 */
class Justification
{
 public:
  Justification(bool inRegion = true) : d_mark(false), d_inRegion(inRegion) {}
  virtual ~Justification() = default;

  /** True if delEh must be invoked to release resources. */
  virtual bool hasDelEh() const { return false; }

  /** Release the resources allocated by this object. */
  virtual void delEh() {}

  /**
   * Mark the antecedents of this justification, using the mark methods of the
   * conflict resolution object.
   */
  virtual void getAntecedents(ConflictResolution& /*cr*/) {}

  /** The theory that produced this object. */
  virtual TheoryId getFromTheory() const { return s_nullTheoryId; }

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

  bool isMarked() const { return d_mark; }

  size_t hash() const { return reinterpret_cast<size_t>(this) >> 3; }

  bool inRegion() const { return d_inRegion; }

  virtual const char* getName() const { return "unknown"; }

 private:
  uint32_t d_mark : 1;
  /** true if the object was allocated in a region */
  uint32_t d_inRegion : 1;
};

/** Resolution of an antecedent against a set of false literals. */
class UnitResolutionJustification : public Justification
{
 public:
  /** Region-allocated variant. */
  UnitResolutionJustification(SmtContext& ctx,
                              Justification* js,
                              size_t numLits,
                              const Literal* lits);

  /** Heap-allocated variant, for justifications attached to lemmas. */
  UnitResolutionJustification(Justification* js,
                              size_t numLits,
                              const Literal* lits);

  ~UnitResolutionJustification() override;

  bool hasDelEh() const override
  {
    return !inRegion() && d_antecedent != nullptr && d_antecedent->hasDelEh();
  }

  void delEh() override
  {
    if (!inRegion() && d_antecedent != nullptr)
    {
      d_antecedent->delEh();
    }
  }

  void getAntecedents(ConflictResolution& cr) override;

  const char* getName() const override { return "unit-resolution"; }

 private:
  Justification* d_antecedent;
  size_t d_numLiterals;
  Literal* d_literals;
};

/** Two nodes with distinct interpreted roots were found equal. */
class EqConflictJustification : public Justification
{
 public:
  EqConflictJustification(ENode* n1, ENode* n2, EqJustification js)
      : d_node1(n1), d_node2(n2), d_js(js)
  {
  }

  void getAntecedents(ConflictResolution& cr) override;

  const char* getName() const override { return "eq-conflict"; }

 private:
  ENode* d_node1;
  ENode* d_node2;
  EqJustification d_js;
};

/** Justification for d_node = root. */
class EqRootPropagationJustification : public Justification
{
 public:
  EqRootPropagationJustification(ENode* n) : d_node(n) {}

  void getAntecedents(ConflictResolution& cr) override;

  const char* getName() const override { return "eq-root"; }

 private:
  ENode* d_node;
};

/** Justification for d_node1 = d_node2. */
class EqPropagationJustification : public Justification
{
 public:
  EqPropagationJustification(ENode* n1, ENode* n2) : d_node1(n1), d_node2(n2) {}

  void getAntecedents(ConflictResolution& cr) override;

  const char* getName() const override { return "eq-propagation"; }

 private:
  ENode* d_node1;
  ENode* d_node2;
};

/** Justification for p(x) <=> p(y), p(x) ==> p(y). */
class MpIffJustification : public Justification
{
 public:
  MpIffJustification(ENode* n1, ENode* n2) : d_node1(n1), d_node2(n2) {}

  void getAntecedents(ConflictResolution& cr) override;

  const char* getName() const override { return "mp-iff"; }

 private:
  /** p(x) */
  ENode* d_node1;
  /** p(y) */
  ENode* d_node2;
};

/** Base class for justifications that carry a set of literals. */
class SimpleJustification : public Justification
{
 public:
  SimpleJustification(SmtContext& ctx, size_t numLits, const Literal* lits);

  void getAntecedents(ConflictResolution& cr) override;

  const char* getName() const override { return "simple"; }

 protected:
  size_t d_numLiterals;
  Literal* d_literals;
};

class SimpleTheoryJustification : public SimpleJustification
{
 public:
  SimpleTheoryJustification(TheoryId fid,
                            SmtContext& ctx,
                            size_t numLits,
                            const Literal* lits)
      : SimpleJustification(ctx, numLits, lits), d_thId(fid)
  {
  }

  TheoryId getFromTheory() const override { return d_thId; }

 protected:
  TheoryId d_thId;
};

class TheoryAxiomJustification : public SimpleTheoryJustification
{
 public:
  TheoryAxiomJustification(TheoryId fid,
                           SmtContext& ctx,
                           size_t numLits,
                           const Literal* lits)
      : SimpleTheoryJustification(fid, ctx, numLits, lits)
  {
  }

  void getAntecedents(ConflictResolution& /*cr*/) override {}

  const char* getName() const override { return "theory-axiom"; }
};

class TheoryPropagationJustification : public SimpleTheoryJustification
{
 public:
  TheoryPropagationJustification(TheoryId fid,
                                 SmtContext& ctx,
                                 size_t numLits,
                                 const Literal* lits,
                                 Literal consequent)
      : SimpleTheoryJustification(fid, ctx, numLits, lits),
        d_consequent(consequent)
  {
  }

  const char* getName() const override { return "theory-propagation"; }

 private:
  Literal d_consequent;
};

class TheoryConflictJustification : public SimpleTheoryJustification
{
 public:
  TheoryConflictJustification(TheoryId fid,
                              SmtContext& ctx,
                              size_t numLits,
                              const Literal* lits)
      : SimpleTheoryJustification(fid, ctx, numLits, lits)
  {
  }

  const char* getName() const override { return "theory-conflict"; }
};

/** Base class for justifications that carry literals and equalities. */
class ExtSimpleJustification : public SimpleJustification
{
 public:
  ExtSimpleJustification(SmtContext& ctx,
                         size_t numLits,
                         const Literal* lits,
                         size_t numEqs,
                         const ENodePair* eqs);

  void getAntecedents(ConflictResolution& cr) override;

  const char* getName() const override { return "ext-simple"; }

 protected:
  size_t d_numEqs;
  ENodePair* d_eqs;
};

class ExtTheorySimpleJustification : public ExtSimpleJustification
{
 public:
  ExtTheorySimpleJustification(TheoryId fid,
                               SmtContext& ctx,
                               size_t numLits,
                               const Literal* lits,
                               size_t numEqs,
                               const ENodePair* eqs)
      : ExtSimpleJustification(ctx, numLits, lits, numEqs, eqs), d_thId(fid)
  {
  }

  TheoryId getFromTheory() const override { return d_thId; }

 protected:
  TheoryId d_thId;
};

class ExtTheoryPropagationJustification : public ExtTheorySimpleJustification
{
 public:
  ExtTheoryPropagationJustification(TheoryId fid,
                                    SmtContext& ctx,
                                    size_t numLits,
                                    const Literal* lits,
                                    size_t numEqs,
                                    const ENodePair* eqs,
                                    Literal consequent)
      : ExtTheorySimpleJustification(fid, ctx, numLits, lits, numEqs, eqs),
        d_consequent(consequent)
  {
  }

  const char* getName() const override { return "ext-theory-propagation"; }

 private:
  Literal d_consequent;
};

class ExtTheoryConflictJustification : public ExtTheorySimpleJustification
{
 public:
  ExtTheoryConflictJustification(TheoryId fid,
                                 SmtContext& ctx,
                                 size_t numLits,
                                 const Literal* lits,
                                 size_t numEqs,
                                 const ENodePair* eqs)
      : ExtTheorySimpleJustification(fid, ctx, numLits, lits, numEqs, eqs)
  {
  }

  const char* getName() const override { return "ext-theory-conflict"; }
};

class ExtTheoryEqPropagationJustification : public ExtTheorySimpleJustification
{
 public:
  ExtTheoryEqPropagationJustification(TheoryId fid,
                                      SmtContext& ctx,
                                      size_t numLits,
                                      const Literal* lits,
                                      size_t numEqs,
                                      const ENodePair* eqs,
                                      ENode* lhs,
                                      ENode* rhs)
      : ExtTheorySimpleJustification(fid, ctx, numLits, lits, numEqs, eqs),
        d_lhs(lhs),
        d_rhs(rhs)
  {
  }

  ExtTheoryEqPropagationJustification(TheoryId fid,
                                      SmtContext& ctx,
                                      ENode* lhs,
                                      ENode* rhs)
      : ExtTheorySimpleJustification(fid, ctx, 0, nullptr, 0, nullptr),
        d_lhs(lhs),
        d_rhs(rhs)
  {
  }

  const char* getName() const override { return "ext-theory-eq-propagation"; }

 private:
  ENode* d_lhs;
  ENode* d_rhs;
};

/**
 * A theory lemma is like a theory axiom, except that it is attached to a
 * lemma clause rather than an auxiliary one. It therefore cannot live in a
 * region, and it is unsafe for it to store literals, since the Boolean
 * variables may be deleted during backtracking.
 */
class TheoryLemmaJustification : public Justification
{
 public:
  TheoryLemmaJustification(TheoryId fid) : Justification(false), d_thId(fid) {}

  void getAntecedents(ConflictResolution& /*cr*/) override {}

  TheoryId getFromTheory() const override { return d_thId; }

  const char* getName() const override { return "theory-lemma"; }

 private:
  TheoryId d_thId;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__JUSTIFICATION_H */
