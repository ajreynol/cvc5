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
 */

#include "z3/statistics.h"

#include <cstring>

namespace cvc5::internal {
namespace z3 {

void Statistics::reset() { std::memset(this, 0, sizeof(Statistics)); }

void Statistics::print(std::ostream& out) const
{
  out << "z3::statistics\n"
      << "  propagations:    " << d_numPropagations << "\n"
      << "  bin propagations:" << d_numBinPropagations << "\n"
      << "  conflicts:       " << d_numConflicts << "\n"
      << "  decisions:       " << d_numDecisions << "\n"
      << "  restarts:        " << d_numRestarts << "\n"
      << "  final checks:    " << d_numFinalChecks << "\n"
      << "  mk bool var:     " << d_numMkBoolVar << "\n"
      << "  del bool var:    " << d_numDelBoolVar << "\n"
      << "  mk enode:        " << d_numMkENode << "\n"
      << "  del enode:       " << d_numDelENode << "\n"
      << "  mk clause:       " << d_numMkClause << "\n"
      << "  del clause:      " << d_numDelClause << "\n"
      << "  add eq:          " << d_numAddEq << "\n"
      << "  dyn ack:         " << d_numDynAck << "\n"
      << "  minimized lits:  " << d_numMinimizedLits << "\n"
      << "  max generation:  " << d_maxGeneration << "\n"
      << "  instances:       " << d_numInstances << "\n"
      << "  lazy instances:  " << d_numLazyInstances << "\n";
}

}  // namespace z3
}  // namespace cvc5::internal
