/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The Z3AssertionPreparation preprocessing pass.
 */

#include "preprocessing/z3/z3_assertion_preparation.h"

#include "options/z3_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/quantifiers/theory_quantifiers.h"
#include "theory/theory_engine.h"
#include "z3/util/assertion_target.h"
#include "z3/util/ast.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

namespace {

/** The core, through the quantifiers engine of the quantifiers theory. */
z3::AssertionTarget* getTarget(TheoryEngine* te)
{
  theory::QuantifiersEngine* qe =
      static_cast<theory::quantifiers::TheoryQuantifiers*>(
          te->theoryOf(theory::THEORY_QUANTIFIERS))
          ->getOwnedQuantifiersEngine();
  z3::AssertionTarget* target = dynamic_cast<z3::AssertionTarget*>(qe);
  Assert(target != nullptr);
  return target;
}

}  // namespace

Z3AssertionPreparation::Z3AssertionPreparation(
    PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "z3-prep"),
      d_nnf(nodeManager()),
      d_connNormalizer(nodeManager()),
      d_assertionRewriter(d_env)
{
  if (options().z3.z3)
  {
    TheoryEngine* te = d_preprocContext->getTheoryEngine();
    getTarget(te)->resetCore(te);
  }
}

PreprocessingPassResult Z3AssertionPreparation::applyInternal(
    AssertionPipeline* assertions)
{
  z3::AssertionTarget* target = getTarget(d_preprocContext->getTheoryEngine());
  // the canonical variables the core and the E-matching engine expect; see
  // z3/util/ast.h
  z3::QuantifierNormalizer& norm = target->getNormalizer();
  bool full = options().z3.z3AssertionPreparation;
  std::vector<Node> prepared;
  // The rest of the pipeline, applied to a formula already in negation
  // normal form.
  auto assertNnf = [&](Node res) {
    if (full)
    {
      res = d_assertionRewriter.rewrite(res);
      res = norm.normalize(d_connNormalizer.normalize(res));
      res = d_assertionRewriter.rewrite(res);
    }
    else
    {
      res = norm.normalize(res);
    }
    // the form cvc5's theories take, and the skolem definitions it needs
    std::vector<Node> defs;
    res = target->preprocessForTheories(res, defs);
    for (const Node& d : defs)
    {
      target->assertPrepared(d);
      prepared.push_back(d);
    }
    target->assertPrepared(res);
    prepared.push_back(res);
  };
  for (const Node& a : assertions->ref())
  {
    if (!full)
    {
      assertNnf(a);
      continue;
    }
    Node res = d_nnf.convert(a);
    // Naming a quantifier below an atom introduces definitions, which
    // nnf_cnf pushes ahead of the formula.
    for (const Node& def : d_nnf.takeDefinitions())
    {
      assertNnf(def);
    }
    assertNnf(res);
  }
  // Each assertion gives at least one prepared formula, and the prepared
  // formulas keep the order of the assertions they come from.
  size_t n = assertions->size();
  Assert(prepared.size() >= n);
  for (size_t i = 0, psize = prepared.size(); i < psize; ++i)
  {
    if (i < n)
    {
      assertions->replace(i, prepared[i], nullptr, TrustId::UNKNOWN_PREPROCESS);
    }
    else
    {
      assertions->push_back(prepared[i]);
    }
  }
  // The skolem definitions are ordinary assertions for the decision
  // heuristic: the indices of the map refer to the assertions before
  // preparation.
  assertions->getIteSkolemMap().clear();
  return assertions->isInConflict() ? PreprocessingPassResult::CONFLICT
                                    : PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
