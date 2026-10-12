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

class SmtContext;

/**
 * The parameters and the SmtContext of the ported Z3 core.
 *
 * The SmtContext still combines the Boolean search with congruence closure,
 * the theory plugins and E-matching, so the --z3 propositional engine
 * (Z3PropEngine) and theory engine (Z3TheoryEngine) cannot yet own separate
 * parts of it. This class is the one owner of that combined state, and
 * Z3TheoryEngine owns this class. It is a temporary stage of the migration
 * described in ARCHITECTURE_PLAN.md (Stage 1A); separating the two sides of
 * the SmtContext is Stage 1B.
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
  /** Get the SmtContext. Requires hasContext(). */
  SmtContext& getContext();
  /** Get the SmtContext. Requires hasContext(). */
  const SmtContext& getContext() const;

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
