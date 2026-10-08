/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Justifications for equality propagation.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_eq_justification.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__EQ_JUSTIFICATION_H
#define CVC5__Z3__EQ_JUSTIFICATION_H

#include "z3/util/literal.h"
#include "z3/util/tagged_ptr.h"

namespace cvc5::internal {
namespace z3 {

class Justification;

/**
 * A proof-like object used to track the dependencies of equality propagation.
 * The point is to make the two common cases -- an asserted equation and
 * congruence -- cost a single word, falling back to a general Justification
 * object otherwise.
 */
class EqJustification
{
 public:
  enum Kind
  {
    /** no justification; only used when proof generation is disabled */
    AXIOM,
    CONGRUENCE,
    /** an asserted equation */
    EQUATION,
    /** fallback */
    JUSTIFICATION
  };

  EqJustification() : d_data(TaggedPtr::boxInt(0, AXIOM)) {}

  /**
   * A justification for the congruence rule. If commutativity is true then
   * this is the combined justification commutativity + congruence.
   */
  explicit EqJustification(bool commutativity)
      : d_data(
            TaggedPtr::boxInt(static_cast<uint32_t>(commutativity), CONGRUENCE))
  {
  }

  explicit EqJustification(Literal l)
      : d_data(TaggedPtr::boxInt(l.index(), EQUATION))
  {
  }

  explicit EqJustification(Justification* js)
      : d_data(TaggedPtr::tag(js, JUSTIFICATION))
  {
  }

  Kind getKind() const { return static_cast<Kind>(d_data.getTag()); }

  Literal getLiteral() const
  {
    Assert(getKind() == EQUATION);
    return toLiteral(d_data.unboxInt());
  }

  Justification* getJustification() const
  {
    Assert(getKind() == JUSTIFICATION);
    return d_data.untag<Justification>();
  }

  bool usedCommutativity() const
  {
    Assert(getKind() == CONGRUENCE);
    return d_data.unboxInt() != 0;
  }

  bool operator==(const EqJustification& other) const
  {
    return d_data == other.d_data;
  }

  bool operator!=(const EqJustification& other) const
  {
    return d_data != other.d_data;
  }

  static EqJustification mkAxiom() { return EqJustification(); }

  static EqJustification mkCg(bool comm = false)
  {
    return EqJustification(comm);
  }

 private:
  TaggedPtr d_data;
};

/** The null justification: a JUSTIFICATION kind with a null pointer. */
inline const EqJustification s_nullEqJustification(
    static_cast<Justification*>(nullptr));

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__EQ_JUSTIFICATION_H */
