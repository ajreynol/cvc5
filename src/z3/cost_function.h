/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cost function of quantifier instantiation.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), files
 * src/parsers/util/cost_parser.cpp and src/ast/cost_evaluator.cpp, recast in
 * cvc5 style. Z3 parses the cost function into its own AST and evaluates that;
 * since the expression is tiny and its variables are fixed, this port parses
 * straight into a small tree of its own.
 *
 * The cost of an instantiation is what decides whether it happens eagerly, is
 * delayed to final check, or is dropped -- which makes it the main brake on
 * matching loops. The default function is "(+ weight generation)".
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__COST_FUNCTION_H
#define CVC5__Z3__COST_FUNCTION_H

#include <memory>
#include <string>
#include <vector>

namespace cvc5::internal {
namespace z3 {

/** The variables a cost function may mention, and their slots in the value
 * array. The numbering is Z3's. */
enum CostVar
{
  CV_CS_FACTOR = 0,
  CV_NESTED_QUANTIFIERS = 1,
  CV_SCOPE = 2,
  CV_TOTAL_INSTANCES = 3,
  CV_PATTERN_WIDTH = 4,
  CV_VARS = 5,
  CV_WEIGHT = 6,
  CV_QUANT_GENERATION = 7,
  CV_GENERATION = 8,
  CV_DEPTH = 9,
  CV_SIZE = 10,
  CV_INSTANCES = 11,
  CV_MAX_TOP_GENERATION = 12,
  CV_MIN_TOP_GENERATION = 13,
  CV_COST = 14,
  CV_NUM_VARS = 15
};

/**
 * A parsed cost function, evaluated over an array of CV_NUM_VARS floats.
 * Everything is computed in floats, including the comparisons, which return
 * one or zero, exactly as Z3 does.
 */
class CostFunction
{
 public:
  /** One node of the parsed expression. */
  struct Expr;

  CostFunction();
  ~CostFunction();

  CostFunction(const CostFunction&) = delete;
  CostFunction& operator=(const CostFunction&) = delete;

  /** Parse s, returning false and leaving this unchanged if it is invalid. */
  bool parse(const std::string& s);

  /** Evaluate the function over the given variable values. */
  float operator()(const std::vector<float>& vals) const;

 private:
  /** The parsed expression, or null if nothing valid was parsed. */
  std::unique_ptr<Expr> d_expr;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__COST_FUNCTION_H */
