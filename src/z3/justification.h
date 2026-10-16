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

class SmtContext;

using JustificationVector = std::vector<Justification*>;

/**
 * A pseudo-proof object, used to track dependencies.
 *
 * Justification objects follow a stack-based allocation policy: they live in
 * the region of the theory side, and are released with the scope that made
 * them.
 */
class Justification
{
 public:
  Justification() : d_mark(false) {}
  virtual ~Justification() = default;

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

 private:
  uint32_t d_mark : 1;
};

/**
 * The justification of an equality cvc5's theories derived; cvc5's master
 * equality engine, which records it, keeps no reasons.
 */
class ExternalEqJustification : public Justification
{
 public:
  ExternalEqJustification() {}
};

/** Two nodes with distinct interpreted roots were found equal. */
class EqConflictJustification : public Justification
{
 public:
  EqConflictJustification(ENode* n1, ENode* n2, EqJustification js)
      : d_node1(n1), d_node2(n2), d_js(js)
  {
  }

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

 private:
  ENode* d_node;
};

/** Justification for d_node1 = d_node2. */
class EqPropagationJustification : public Justification
{
 public:
  EqPropagationJustification(ENode* n1, ENode* n2) : d_node1(n1), d_node2(n2) {}

 private:
  ENode* d_node1;
  ENode* d_node2;
};

/** Justification for p(x) <=> p(y), p(x) ==> p(y). */
class MpIffJustification : public Justification
{
 public:
  MpIffJustification(ENode* n1, ENode* n2) : d_node1(n1), d_node2(n2) {}

 private:
  /** p(x) */
  ENode* d_node1;
  /** p(y) */
  ENode* d_node2;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__JUSTIFICATION_H */
