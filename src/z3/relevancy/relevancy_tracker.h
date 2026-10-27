/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module of the theory engine that gives the ported Z3 core the
 * assignment of the SAT solver.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__RELEVANCY__RELEVANCY_TRACKER_H
#define CVC5__Z3__RELEVANCY__RELEVANCY_TRACKER_H

#include "context/cdlist.h"
#include "context/cdo.h"
#include "theory/theory_engine_module.h"

namespace cvc5::internal {

namespace theory {
class TheoryState;
}

namespace z3 {

class Z3Module;

/**
 * Like cvc5's RelevanceManager, a module of the theory engine that tracks
 * which parts of the Boolean structure matter in the current assignment, for
 * the ported core: Z3's relevancy (level 2), which decides what the core
 * matches and instantiates over, is computed by the Boolean side of the core
 * from the value of every atom the SAT solver asserts, whichever theory the
 * atom belongs to, and from the values of Boolean variables.
 *
 * This module is notified of every literal the SAT solver asserts to the
 * theory engine. The literals are queued, in the SAT context, and given to
 * the core in order when the quantifiers engine is checked (flush), which is
 * when the core is run.
 */
class RelevancyTracker : public theory::TheoryEngineModule
{
 public:
  /**
   * The literals are given to core, which assigns them on its Boolean side
   * (PropCore).
   */
  RelevancyTracker(Env& env, TheoryEngine* engine, Z3Module& core);

  bool needsFacts() override { return true; }
  /** Queue the literal. */
  void notifyFact(TNode literal) override;

  /**
   * Give the queued literals to the core, in order, while state is not in
   * conflict.
   */
  void flush(const theory::TheoryState& state);

 private:
  /** The core, which owns this module. */
  Z3Module& d_core;
  /** The literals the SAT solver asserted, in order. */
  context::CDList<Node> d_facts;
  /** The index in d_facts of the first literal not given to the core. */
  context::CDO<size_t> d_factsHead;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__RELEVANCY__RELEVANCY_TRACKER_H */
