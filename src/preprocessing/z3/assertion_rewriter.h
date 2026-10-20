/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The rewriting Z3 applies to its assertions around NNF.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), and
 * recast in cvc5 style. Used only to prepare the assertions for the ported
 * core, see Z3AssertionPreparation.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__Z3__ASSERTION_REWRITER_H
#define CVC5__PREPROCESSING__Z3__ASSERTION_REWRITER_H

#include <unordered_map>

#include "expr/node.h"

namespace cvc5::internal {

class Env;

namespace z3 {

/**
 * Runs the rewriter over an assertion, which is Z3's
 * asserted_formulas::m_reduce_asserted_formulas. Z3's reduce() applies it
 * twice -- immediately after NNF and again after pattern inference -- and
 * nnf_cnf applies it to every formula it produces before pushing it. Without
 * it the structure that NNF and skolemization build is never simplified: a
 * disjunct that is itself a disjunction stays nested and costs the core an
 * auxiliary Boolean variable and a gate, a conjunct of a conjunction likewise,
 * and nothing that has become constant is folded away.
 *
 * The ground parts go to cvc5's rewriter. A quantifier is rebuilt from its
 * rewritten body rather than handed to the rewriter whole, because cvc5's
 * quantifiers rewriter restructures quantifiers -- miniscoping, variable
 * elimination, prenexing -- and in Z3 that is the job of separate passes of
 * reduce(), each with its own parameter, not of the rewriter.
 */
class AssertionRewriter
{
 public:
  AssertionRewriter(Env& env) : d_env(env) {}

  Node rewrite(TNode n);

 private:
  Env& d_env;
  std::unordered_map<Node, Node> d_cache;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__Z3__ASSERTION_REWRITER_H */
