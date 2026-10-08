/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Justifications for Boolean propagation.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_b_justification.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__B_JUSTIFICATION_H
#define CVC5__Z3__B_JUSTIFICATION_H

#include <ostream>

#include "z3/clause.h"
#include "z3/util/literal.h"
#include "z3/util/tagged_ptr.h"

namespace cvc5::internal {
namespace z3 {

class Justification;

/**
 * A proof-like object used to track the dependencies of Boolean propagation.
 * The point is to make the common case -- unit propagation out of a clause or
 * a binary clause -- cost a single word.
 */
class BJustification
{
 public:
  enum Kind
  {
    /** a clause of arbitrary size */
    CLAUSE,
    /** a binary clause, represented by its other literal */
    BIN_CLAUSE,
    /** no justification; only used when proof generation is disabled */
    AXIOM,
    /** fallback */
    JUSTIFICATION
  };

  BJustification() : d_data(TaggedPtr::boxInt(0, AXIOM)) {}

  explicit BJustification(Clause* c) : d_data(TaggedPtr::tag(c, CLAUSE)) {}

  explicit BJustification(Literal l)
      : d_data(TaggedPtr::boxInt(l.index(), BIN_CLAUSE))
  {
  }

  explicit BJustification(Justification* js)
      : d_data(TaggedPtr::tag(js, JUSTIFICATION))
  {
    Assert(js != nullptr);
  }

  Kind getKind() const { return static_cast<Kind>(d_data.getTag()); }

  Clause* getClause() const
  {
    Assert(getKind() == CLAUSE);
    return d_data.untag<Clause>();
  }

  Justification* getJustification() const
  {
    Assert(getKind() == JUSTIFICATION);
    return d_data.untag<Justification>();
  }

  Literal getLiteral() const
  {
    Assert(getKind() == BIN_CLAUSE);
    return toLiteral(d_data.unboxInt());
  }

  bool operator==(const BJustification& other) const
  {
    return d_data == other.d_data;
  }

  bool operator!=(const BJustification& other) const
  {
    return !operator==(other);
  }

  static BJustification mkAxiom() { return BJustification(); }

 private:
  TaggedPtr d_data;
};

/** The null justification: a CLAUSE kind with a null clause. */
inline const BJustification s_nullBJustification(static_cast<Clause*>(nullptr));

inline std::ostream& operator<<(std::ostream& out, BJustification::Kind k)
{
  switch (k)
  {
    case BJustification::CLAUSE: return out << "clause";
    case BJustification::BIN_CLAUSE: return out << "bin_clause";
    case BJustification::AXIOM: return out << "axiom";
    case BJustification::JUSTIFICATION: return out << "theory";
  }
  return out;
}

using JustifiedLiteral = std::pair<Literal, BJustification>;

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__B_JUSTIFICATION_H */
