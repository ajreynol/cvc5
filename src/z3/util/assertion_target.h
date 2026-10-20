/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * What the preparation of assertions needs from the ported Z3 core.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__ASSERTION_TARGET_H
#define CVC5__Z3__UTIL__ASSERTION_TARGET_H

#include <vector>

#include "expr/node.h"

namespace cvc5::internal {

class TheoryEngine;

namespace z3 {

class QuantifierNormalizer;

/**
 * The core as Z3AssertionPreparation, the preprocessing pass, sees it: the
 * quantifiers engine with --z3 (Z3QuantifiersEngine) implements it.
 */
class AssertionTarget
{
 public:
  virtual ~AssertionTarget() = default;
  /**
   * Make a fresh core, for the theory engine te, after its prop engine was
   * made.
   */
  virtual void resetCore(TheoryEngine* te) = 0;
  /**
   * The canonicalizer for quantifiers of the core, which also canonicalizes
   * the instances; see z3/util/ast.h.
   */
  virtual QuantifierNormalizer& getNormalizer() = 0;
  /**
   * Map n to the form cvc5's theories take, adding to defs the definitions
   * of the skolems introduced.
   */
  virtual Node preprocessForTheories(TNode n, std::vector<Node>& defs) = 0;
  /** Assert the prepared formula n to the core. */
  virtual void assertPrepared(TNode n) = 0;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__ASSERTION_TARGET_H */
