/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The preparation of preprocessed assertions for the ported Z3 core.
 *
 * Not ported from Z3: this is cvc5 integration code, which sequences the
 * ported normalizations in the order Z3's own preprocessing applies them.
 */

#include "z3/assertion_preparation.h"

#include "options/z3_options.h"
#include "smt/env.h"
#include "z3/ast.h"
#include "z3/quantifier_manager.h"
#include "z3/smt_context.h"

namespace cvc5::internal {
namespace z3 {

AssertionPreparation::AssertionPreparation(Env& env) : EnvObj(env) {}

void AssertionPreparation::apply(SmtContext& ctx,
                                 PropCore& core,
                                 const std::vector<Node>& assertions,
                                 std::vector<Node>* prepared)
{
  // Rewrite the quantifiers of each assertion over the canonical variables
  // the core and the E-matching engine expect; see z3/ast.h.
  QuantifierNormalizer& norm = ctx.getNormalizer();
  // Z3 infers patterns for the quantifiers that carry no :pattern annotation
  // as part of its own preprocessing, so that step is run here, on the
  // normalized form, before the formula reaches the core.
  PatternInference& pi = ctx.getPatternInference();
  ConnectiveNormalizer& cn = ctx.getConnectiveNormalizer();
  // The core relies on every universal quantifier occurring positively, which
  // Z3 establishes with its own nnf pass; see z3/nnf.h.
  Nnf& nnf = ctx.getNnf();
  // Z3's asserted_formulas::reduce() rewrites every formula right after NNF
  // and again after pattern inference; nnf_cnf rewrites each formula it
  // produces as well. Both are here, around the rest of the pipeline.
  AssertionRewriter& rw = ctx.getAssertionRewriter();
  const bool doRewrite = options().z3.z3RewriteAssertions;
  // Z3's ng_lift_ite, which reduce() runs after the rewrite that follows NNF
  // and follows with another rewrite (reduce_and_solve); see
  // z3/push_app_ite.h.
  const bool doLiftIte = ctx.getParams().d_ngLiftIte != Params::LI_NONE;
  NgPushAppIte& lift = ctx.getNgPushAppIte();
  // The rest of the pipeline, applied to a formula already in negation
  // normal form.
  auto assertNnf = [&](Node res, Node original) {
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
    res = doRewrite ? rw.rewrite(res) : res;
    if (!original.isNull())
    {
      ctx.getQuantifierManager()->recordQuantifierOrigins(original, res);
    }
    core.assertFormula(res);
    if (prepared != nullptr)
    {
      prepared->push_back(res);
    }
  };
  for (const Node& a : assertions)
  {
    Node res = nnf.convert(a);
    // Naming a quantifier below an atom introduces definitions, which
    // nnf_cnf pushes ahead of the formula.
    for (const Node& def : nnf.takeDefinitions())
    {
      assertNnf(def, Node::null());
    }
    assertNnf(res, a);
  }
}

}  // namespace z3
}  // namespace cvc5::internal
