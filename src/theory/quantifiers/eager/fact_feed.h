/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module of the theory engine that feeds the eager E-matching core the
 * literals the SAT solver asserts.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__FACT_FEED_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__FACT_FEED_H

#include "context/cdlist.h"
#include "context/cdo.h"
#include "theory/theory_engine_module.h"

namespace cvc5::internal {

namespace theory {
class TheoryState;
}

namespace theory::quantifiers::eager {

class EagerEMatching;

/**
 * The feed of the facts of cvc5 to the core: the core's E-graph and Boolean
 * side, and so its relevancy (level 2, see RelevancyPropagator), follow the
 * value of every atom the SAT solver asserts, whichever theory the atom
 * belongs to, and the values of Boolean variables.
 *
 * This module is notified of every literal the SAT solver asserts to the
 * theory engine. The literals are queued, in the SAT context, and given to
 * the core in order when the quantifiers engine is checked (flush), which is
 * when the core is run.
 */
class FactFeed : public theory::TheoryEngineModule
{
 public:
  /**
   * The literals are given to core, which assigns them on its Boolean side
   * (PropCore).
   */
  FactFeed(Env& env, TheoryEngine* engine, EagerEMatching& core);

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
  EagerEMatching& d_core;
  /** The literals the SAT solver asserted, in order. */
  context::CDList<Node> d_facts;
  /** The index in d_facts of the first literal not given to the core. */
  context::CDO<size_t> d_factsHead;
};

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER__FACT_FEED_H */
