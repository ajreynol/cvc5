/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Basic types for the ported Z3 SMT engine.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * files src/smt/smt_types.h and src/util/lbool.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__TYPES_H
#define CVC5__Z3__TYPES_H

#include <cstdint>
#include <ostream>
#include <utility>
#include <vector>

#include "theory/theory_id.h"

namespace cvc5::internal {
namespace z3 {

/**
 * A lifted Boolean. The numeric values matter: negation is arithmetic
 * negation, and the ordering FALSE < UNDEF < TRUE is relied upon.
 */
enum LBool : int8_t
{
  L_FALSE = -1,
  L_UNDEF = 0,
  L_TRUE = 1
};

inline LBool operator~(LBool lb)
{
  return static_cast<LBool>(-static_cast<int8_t>(lb));
}

inline LBool toLBool(bool b)
{
  return static_cast<LBool>(static_cast<int8_t>(b) * 2 - 1);
}

std::ostream& operator<<(std::ostream& out, LBool b);

/**
 * A theory identifier. We reuse cvc5's TheoryId, which plays the role of
 * Z3's family_id: it is the key that maps an operator to the theory that
 * owns it, and the index into the core's table of theory plugins.
 */
using TheoryId = theory::TheoryId;

/** The absence of a theory. Z3 calls this null_family_id. */
constexpr TheoryId s_nullTheoryId = theory::THEORY_LAST;

/** The number of theory slots the core reserves. */
constexpr size_t s_numTheories = static_cast<size_t>(theory::THEORY_LAST);

/** A theory-local variable, interpreted by the owning theory. */
using TheoryVar = int32_t;

constexpr TheoryVar s_nullTheoryVar = -1;

class ENode;

using ENodeVector = std::vector<ENode*>;
using ENodePair = std::pair<ENode*, ENode*>;
using ENodePairVector = std::vector<ENodePair>;

class Theory;
class Justification;
class ModelGenerator;
class SmtContext;

/** The outcome of a theory's final check. */
enum FinalCheckStatus
{
  /** The theory is satisfied with the current assignment. */
  FC_DONE,
  /** The theory made progress and wants the search to continue. */
  FC_CONTINUE,
  /** The theory cannot decide; the result will be "unknown". */
  FC_GIVEUP
};

std::ostream& operator<<(std::ostream& out, FinalCheckStatus st);

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__TYPES_H */
