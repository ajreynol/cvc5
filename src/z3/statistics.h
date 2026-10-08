/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Statistics of the ported Z3 SMT core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_statistics.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__STATISTICS_H
#define CVC5__Z3__STATISTICS_H

#include <cstdint>
#include <ostream>

namespace cvc5::internal {
namespace z3 {

struct Statistics
{
  uint64_t d_numPropagations;
  uint64_t d_numBinPropagations;
  uint64_t d_numConflicts;
  uint64_t d_numSatConflicts;
  uint64_t d_numDecisions;
  uint64_t d_numAddEq;
  uint64_t d_numRestarts;
  uint64_t d_numFinalChecks;
  uint64_t d_numMkBoolVar;
  uint64_t d_numDelBoolVar;
  uint64_t d_numMkENode;
  uint64_t d_numDelENode;
  uint64_t d_numMkClause;
  uint64_t d_numDelClause;
  uint64_t d_numMkBinClause;
  uint64_t d_numMkLits;
  uint64_t d_numDynAck;
  uint64_t d_numDelDynAck;
  uint64_t d_numInterfaceEqs;
  uint64_t d_maxGeneration;
  uint64_t d_numMinimizedLits;
  uint64_t d_numChecks;
  uint64_t d_numSimplifications;
  uint64_t d_numDelClauses;
  uint64_t d_numAssignments;
  /** quantifier instantiations produced by E-matching */
  uint64_t d_numInstances;
  /** instantiations dropped because their cost exceeded the lazy threshold */
  uint64_t d_numLazyInstances;

  Statistics() { reset(); }

  void reset();

  void print(std::ostream& out) const;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__STATISTICS_H */
