/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Construction of the theory and propositional engines of an SmtSolver.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__ENGINE_FACTORY_H
#define CVC5__SMT__ENGINE_FACTORY_H

#include <memory>

namespace cvc5::internal {

class Env;
class TheoryEngine;

namespace prop {
class PropEngine;
}

namespace smt {

/**
 * Construction of the engines that SmtSolver drives. This is the only place
 * where the implementation of the engines is selected: SmtSolver itself is
 * the same for every implementation, and uses the engines only through the
 * contracts of TheoryEngine and PropEngine.
 *
 * The engines come in compatible pairs. By default, they are cvc5's own
 * CDCL(T) engines. With --z3, they are the engines of the ported Z3 core,
 * see z3/z3_theory_engine.h and z3/z3_prop_engine.h, which share one search
 * state and so can only be used together.
 */
class EngineFactory
{
 public:
  /** Make the theory engine selected by the options of env. */
  static std::unique_ptr<TheoryEngine> mkTheoryEngine(Env& env);
  /**
   * Make the propositional engine paired with te, which must have been made
   * by mkTheoryEngine.
   */
  static std::unique_ptr<prop::PropEngine> mkPropEngine(Env& env,
                                                        TheoryEngine* te);
};

}  // namespace smt
}  // namespace cvc5::internal

#endif /* CVC5__SMT__ENGINE_FACTORY_H */
