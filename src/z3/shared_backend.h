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
 * The parameters and the two sides of the ported Z3 core: a propositional
 * side, PropCore, which in host mode mirrors cvc5's assignment, and a theory
 * side, SmtContext (the E-graph, relevancy and the quantifier stack). The
 * PropCore is allocated inside the SmtContext, so that the Boolean queries
 * the theory side makes on its hot paths stay cheap.
 *
 * The quantifiers engine (Z3QuantifiersEngine) owns this class for as long
 * as the theory engine exists. SmtSolver replaces its PropEngine on reset-assertions, and each new
 * Z3HostedPropEngine replaces the SmtContext when it is initialized.
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
  /** Get the theory side. Requires that resetContext has been called. */
  SmtContext& getContext();
  /** Get the propositional side. Requires that resetContext has been called. */
  PropCore& getPropCore();

 private:
  /** The parameters of the core. These must outlive d_ctx. */
  Params d_params;
  /** The core. */
  std::unique_ptr<SmtContext> d_ctx;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__SHARED_BACKEND_H */
