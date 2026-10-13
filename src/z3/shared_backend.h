/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The search state shared by the propositional and theory engines of the
 * ported Z3 core.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__SHARED_BACKEND_H
#define CVC5__Z3__SHARED_BACKEND_H

#include <memory>

#include "smt/env_obj.h"
#include "z3/params.h"

namespace cvc5::internal {
namespace z3 {

class PropCore;
class SmtContext;

/**
 * The parameters and the two sides of the ported Z3 core.
 *
 * The core is divided into a propositional side, PropCore, and a theory side,
 * SmtContext, with the interface between them described in
 * PROP_THEORY_SPLIT.md. Z3PropEngine drives the propositional side, which in
 * turn drives the theory side. The PropCore is allocated inside the
 * SmtContext, so that the Boolean queries the theory side makes on its hot
 * paths cost no more than before the division; this class owns the two
 * together, and Z3TheoryEngine owns this class.
 *
 * The lifetimes follow those of the native engines. SmtSolver keeps its
 * TheoryEngine for as long as it exists, and so the parameters live as long as
 * the SmtSolver does: auto configuration writes to them on the first check,
 * and a context made after reset-assertions sees what it wrote. SmtSolver
 * replaces its PropEngine on reset-assertions, and each new Z3PropEngine
 * replaces the SmtContext when it is initialized. Neither engine keeps a
 * reference to the SmtContext, so neither can see a replaced one.
 */
class SharedBackend : protected EnvObj
{
 public:
  SharedBackend(Env& env);
  ~SharedBackend();
  /**
   * Discard the current SmtContext, if any, and make a fresh one over the
   * same parameters.
   */
  void resetContext();
  /** Whether resetContext has been called. */
  bool hasContext() const { return d_ctx != nullptr; }
  /**
   * Get the theory side, the SmtContext. Requires hasContext(). Z3PropEngine
   * uses it only to prepare assertions, whose utilities belong to it.
   */
  SmtContext& getContext();
  /** Get the SmtContext. Requires hasContext(). */
  const SmtContext& getContext() const;
  /**
   * Get the propositional side, which Z3PropEngine drives. Requires
   * hasContext().
   */
  PropCore& getPropCore();
  /** Get the propositional side. Requires hasContext(). */
  const PropCore& getPropCore() const;

 private:
  /**
   * The parameters of the core, defaulted as in Z3. These must outlive
   * d_ctx, which refers to them.
   */
  Params d_params;
  /** The core. */
  std::unique_ptr<SmtContext> d_ctx;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__SHARED_BACKEND_H */
