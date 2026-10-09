/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An alternative solver for SMT queries that runs a port of Z3's SMT core.
 */

#include "smt/z3_smt_solver.h"

#include "options/base_options.h"
#include "options/z3_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "smt/env.h"
#include "smt/logic_exception.h"
#include "z3/ast.h"
#include "z3/smt_context.h"

namespace cvc5::internal {
namespace smt {

Z3SmtSolver::Z3SmtSolver(Env& env, SolverEngineStatistics& stats)
    : SmtSolver(env, stats), d_ctx(nullptr)
{
  d_params.initialize(env.getOptions());
}

Z3SmtSolver::~Z3SmtSolver() {}

void Z3SmtSolver::finishInit()
{
  // Build the TheoryEngine and PropEngine, which the preprocessor and the
  // model-building paths still require.
  SmtSolver::finishInit();
  d_ctx.reset(new z3::SmtContext(d_env, d_params));
}

void Z3SmtSolver::resetAssertions()
{
  SmtSolver::resetAssertions();
  d_ctx.reset(new z3::SmtContext(d_env, d_params));
}

void Z3SmtSolver::interrupt()
{
  SmtSolver::interrupt();
  if (d_ctx != nullptr)
  {
    d_ctx->interrupt();
  }
}

void Z3SmtSolver::pushPropContext()
{
  Assert(d_ctx != nullptr);
  d_ctx->push();
}

void Z3SmtSolver::popPropContext()
{
  Assert(d_ctx != nullptr);
  d_ctx->pop(1);
}

void Z3SmtSolver::resetTrail()
{
  if (d_ctx != nullptr)
  {
    d_ctx->popToBaseLvl();
  }
}

void Z3SmtSolver::assertToInternal(preprocessing::AssertionPipeline& ap)
{
  Assert(d_ctx != nullptr);
  // Rewrite the quantifiers of each assertion over the canonical variables
  // the core and the E-matching engine expect; see z3/ast.h.
  z3::QuantifierNormalizer& norm = d_ctx->getNormalizer();
  // Z3 infers patterns for the quantifiers that carry no :pattern annotation
  // as part of its own preprocessing, so that step is run here, on the
  // normalized form, before the formula reaches the core.
  z3::PatternInference& pi = d_ctx->getPatternInference();
  z3::ConnectiveNormalizer& cn = d_ctx->getConnectiveNormalizer();
  // The core relies on every universal quantifier occurring positively, which
  // Z3 establishes with its own nnf pass; see z3/nnf.h.
  z3::Nnf& nnf = d_ctx->getNnf();
  // Z3's asserted_formulas::reduce() rewrites every formula right after NNF
  // and again after pattern inference; nnf_cnf rewrites each formula it
  // produces as well. Both are here, around the rest of the pipeline.
  z3::AssertionRewriter& rw = d_ctx->getAssertionRewriter();
  const bool doRewrite = options().z3.z3RewriteAssertions;
  // Z3's ng_lift_ite, which reduce() runs after the rewrite that follows NNF
  // and follows with another rewrite (reduce_and_solve); see
  // z3/push_app_ite.h.
  const bool doLiftIte =
      options().z3.z3NgLiftIte != options::Z3LiftIteMode::NONE;
  z3::NgPushAppIte& lift = d_ctx->getNgPushAppIte();
  for (const Node& a : ap.ref())
  {
    Node res = nnf.convert(a);
    if (doRewrite)
    {
      res = rw.rewrite(res);
    }
    if (doLiftIte)
    {
      Node lifted = lift.apply(res);
      if (lifted != res)
      {
        res = doRewrite ? rw.rewrite(lifted) : lifted;
      }
    }
    res = pi.apply(norm.normalize(cn.normalize(res)));
    d_ctx->assertFormula(doRewrite ? rw.rewrite(res) : res);
  }
}

Result Z3SmtSolver::checkSatInternal()
{
  Assert(d_ctx != nullptr);
  if (options().base.preprocessOnly)
  {
    return Result(Result::UNKNOWN, UnknownExplanation::REQUIRES_FULL_CHECK);
  }
  z3::LBool r = d_ctx->check();
  switch (r)
  {
    case z3::L_TRUE: return Result(Result::SAT);
    case z3::L_FALSE: return Result(Result::UNSAT);
    default: break;
  }
  verbose(1) << "z3: unknown: " << d_ctx->getLastSearchFailure() << ": "
             << d_ctx->getReasonUnknown() << std::endl;
  UnknownExplanation why = UnknownExplanation::UNKNOWN_REASON;
  switch (d_ctx->getLastSearchFailure())
  {
    case z3::MEMOUT:
    case z3::RESOURCE_LIMIT: why = UnknownExplanation::RESOURCEOUT; break;
    case z3::CANCELED: why = UnknownExplanation::INTERRUPTED; break;
    case z3::NUM_CONFLICTS:
    case z3::THEORY:
    case z3::QUANTIFIERS: why = UnknownExplanation::INCOMPLETE; break;
    default: break;
  }
  return Result(Result::UNKNOWN, why);
}

}  // namespace smt
}  // namespace cvc5::internal
