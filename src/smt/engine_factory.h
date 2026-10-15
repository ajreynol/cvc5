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

#include <map>
#include <memory>
#include <vector>

#include "expr/node.h"

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
  /** Read untrusted instantiation hints from any of the port's engine modes. */
  static void getZ3InstantiationTermVectors(
      Env& env,
      TheoryEngine* te,
      std::map<Node, std::vector<std::vector<Node>>>& insts);
  /** Make the theory engine selected by the options of env. */
  static std::unique_ptr<TheoryEngine> mkTheoryEngine(Env& env);
  /**
   * Add the theories of te, which must have been made by mkTheoryEngine, if
   * the options of env select other implementations than cvc5's own
   * theories (--z3-theory-engine=cvc5). Returns false if they do not, in
   * which case the caller adds cvc5's theories.
   */
  static bool addTheories(Env& env, TheoryEngine* te);
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
