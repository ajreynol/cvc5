/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved. See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************/

#include "smt/sort_parameter_manager.h"

#include <algorithm>

#include "expr/dtype.h"
#include "expr/node_algorithm.h"
#include "expr/sort_parameter_converter.h"
#include "expr/sort_to_term.h"
#include "options/parser_options.h"
#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "proof/lazy_proof.h"
#include "smt/assertions.h"
#include "smt/env.h"
#include "theory/rewriter.h"
#include "theory/trust_substitutions.h"
#include "util/resource_manager.h"

namespace cvc5::internal::smt {

SortParameterManager::SortParameterManager(Env& env)
    : EnvObj(env),
      d_declarations(userContext()),
      d_processed(userContext()),
      d_instances(userContext())
{
}
SortParameterManager::~SortParameterManager() = default;

void SortParameterManager::declareSort(TypeNode type)
{
  if (options().parser.globalDeclarations)
  {
    d_globalDeclarations.push_back(type);
  }
  else if (userContext()->getLevel() == 0)
  {
    d_pendingDeclarations.push_back(type);
  }
  else
  {
    d_declarations.push_back(type);
  }
}

void SortParameterManager::finishInit()
{
  Assert(userContext()->getLevel() > 0);
  for (TypeNode type : d_pendingDeclarations) d_declarations.push_back(type);
  d_pendingDeclarations.clear();
}

void SortParameterManager::instantiate(
    Assertions& assertions, preprocessing::AssertionPipeline& pipeline)
{
  NodeManager* nm = nodeManager();
  d_complete = true;
  if (!nm->hasSortParameters())
  {
    return;
  }
  // Recompute the signature at check time. In particular, a sort declared
  // after an assertion (possibly at a deeper level) supplies new instances.
  std::unordered_set<TypeNode> types;
  types.insert(nm->booleanType());
  if (logicInfo().isTheoryEnabled(theory::THEORY_ARITH))
  {
    if (logicInfo().areIntegersUsed()) types.insert(nm->integerType());
    if (logicInfo().areRealsUsed()) types.insert(nm->realType());
  }
  if (logicInfo().isTheoryEnabled(theory::THEORY_STRINGS))
  {
    types.insert(nm->stringType());
    types.insert(nm->regExpType());
  }
  if (logicInfo().isTheoryEnabled(theory::THEORY_FP))
  {
    types.insert(nm->roundingModeType());
  }
  bool finite = !logicInfo().isHigherOrder();
  for (theory::TheoryId id : {theory::THEORY_ARRAYS,
                              theory::THEORY_BV,
                              theory::THEORY_FP,
                              theory::THEORY_FF,
                              theory::THEORY_SETS,
                              theory::THEORY_BAGS,
                              theory::THEORY_STRINGS})
  {
    finite = finite && !logicInfo().isTheoryEnabled(id);
  }
  std::vector<Node> schemas;
  for (Node n : assertions.getAssertionList())
  {
    SortParameterConverter::collectTypes(n, types);
    if (expr::hasSortParameter(n)) schemas.push_back(n);
  }
  std::vector<TypeNode> declarations(d_declarations.begin(),
                                     d_declarations.end());
  declarations.insert(declarations.end(),
                      d_globalDeclarations.begin(),
                      d_globalDeclarations.end());
  for (TypeNode type : declarations)
  {
    // A dummy bound variable is only used for traversing the type graph.
    if (!type.isUninterpretedSortConstructor())
    {
      SortParameterConverter::collectTypes(nm->mkBoundVar(type), types);
    }
    else
      types.insert(type);
  }
  d_groundSorts.clear();
  std::unordered_set<TypeNode> localParameters;
  for (TypeNode type : types)
  {
    if (type.isDatatype() && type.getDType().isParametric())
    {
      auto parameters = type.getDType().getParameters();
      localParameters.insert(parameters.begin(), parameters.end());
    }
  }
  for (TypeNode type : types)
  {
    if (type.isUninterpretedSortConstructor()
        || (type.isDatatype() && type.getDType().isParametric()))
    {
      finite = false;
    }
    // Only first-class SMT sorts can instantiate parameters. Internal sort
    // tags and the uninstantiated body of a parametric datatype are excluded.
    if (!type.isFirstClass() || type.hasSortParameter()
        || localParameters.count(type)
        || (type.isFunction() && !logicInfo().isHigherOrder())
        || type.isUninterpretedSortConstructor()
        || (type.isDatatype() && type.getDType().isParametric()
            && (type.getKind() != Kind::PARAMETRIC_DATATYPE
                || !type.isInstantiated()))
        || (type.getKind() == Kind::TYPE_CONSTANT && !type.isBoolean()
            && !type.isInteger() && !type.isReal() && !type.isString()
            && !type.isRegExp() && !type.isRoundingMode()))
    {
      continue;
    }
    d_groundSorts.push_back(type);
  }
  std::sort(d_groundSorts.begin(), d_groundSorts.end());
  // Bool is always present, so there is at least one ground instantiation.
  Assert(!d_groundSorts.empty());
  if (schemas.empty()) return;
  d_complete = finite;
  if (d_env.isProofProducing() && !d_proof)
  {
    d_proof = std::make_unique<LazyCDProof>(d_env, nullptr, userContext());
  }
  const auto definitions = assertions.getCurrentAssertionListDefitions();
  size_t remaining = options().smt.sortInstantiationLimit;
  bool nontrivial = false;
  for (Node schema : schemas)
  {
    // A schematic tautology needs no enumeration of its sort instances.
    Node rewritten = rewrite(schema);
    if (rewritten.isConst() && rewritten.getConst<bool>()) continue;
    nontrivial = true;
    std::vector<TypeNode> parameters =
        SortParameterConverter::getParameters(schema);
    std::vector<size_t> indices(parameters.size(), 0);
    bool done = false;
    while (!done)
    {
      if (remaining == 0)
      {
        d_complete = false;
        break;
      }
      --remaining;
      d_env.getResourceManager()->spendResource(Resource::PreprocessStep);
      std::vector<TypeNode> replacements;
      std::vector<Node> proofArgs;
      for (size_t i = 0; i < parameters.size(); ++i)
      {
        replacements.push_back(d_groundSorts[indices[i]]);
        proofArgs.push_back(nm->mkConst(SortToTerm(parameters[i])));
        proofArgs.push_back(nm->mkConst(SortToTerm(replacements.back())));
      }
      SortParameterConverter converter(nm, parameters, replacements);
      Node instance = converter.convert(schema, false);
      Assert(!expr::hasSortParameter(instance));
      if (d_processed.insert(instance))
      {
        d_instances.push_back(instance);
        if (d_proof)
        {
          d_proof->addStep(
              instance, ProofRule::INSTANTIATE_SORTS, {schema}, proofArgs);
        }
        // Definitions are substitutions, just as in Assertions::addFormula.
        // Additional instances of a definition with the same left-hand side
        // remain constraints (its body may contain more sort parameters).
        if (definitions.count(schema) && instance.getKind() == Kind::EQUAL
            && instance[0].isVar()
            && !expr::hasSubterm(instance[1], instance[0]))
        {
          theory::TrustSubstitutionMap& substitutions =
              d_env.getTopLevelSubstitutions();
          if (!substitutions.get().hasSubstitution(instance[0]))
          {
            substitutions.addSubstitution(
                instance[0], instance[1], d_proof.get());
          }
        }
        pipeline.push_back(instance, false, d_proof.get());
      }
      size_t i = 0;
      for (; i < indices.size(); ++i)
      {
        if (++indices[i] < d_groundSorts.size()) break;
        indices[i] = 0;
      }
      done = i == indices.size();
    }
  }
  if (!nontrivial) d_complete = true;
  if (!d_complete) pipeline.markModelUnsound();
}

}  // namespace cvc5::internal::smt
