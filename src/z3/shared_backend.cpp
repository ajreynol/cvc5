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

#include "z3/shared_backend.h"

#include "smt/env.h"
#include "z3/smt_context.h"

namespace cvc5::internal {
namespace z3 {

SharedBackend::SharedBackend(Env& env) : EnvObj(env), d_ctx(nullptr)
{
  d_params.initialize(env.getOptions());
}

SharedBackend::~SharedBackend() {}

void SharedBackend::resetContext()
{
  d_ctx.reset(new SmtContext(d_env, d_params));
}

SmtContext& SharedBackend::getContext()
{
  Assert(d_ctx != nullptr);
  return *d_ctx;
}

const SmtContext& SharedBackend::getContext() const
{
  Assert(d_ctx != nullptr);
  return *d_ctx;
}

}  // namespace z3
}  // namespace cvc5::internal
