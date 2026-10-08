/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Negation normal form with skolemization, over the Boolean structure that
 * contains quantifiers.
 *
 * The ported core relies on Z3's invariant that every universal quantifier
 * occurs positively in the input: a Boolean variable of a quantifier that is
 * assigned false is simply ignored (see SmtContext::assignQuantifier and the
 * same comment in Z3's smt_context.cpp). Z3 establishes the invariant in its
 * own preprocessing, with the nnf pass that asserted_formulas::reduce()
 * invokes; cvc5's preprocessor does not, so the step is done here.
 *
 * Only the parts of a formula that contain a quantifier are rewritten, so
 * what cvc5's preprocessor produced for the ground part is left untouched.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__NNF_H
#define CVC5__Z3__NNF_H

#include <unordered_map>
#include <vector>

#include "expr/node.h"

namespace cvc5::internal {

class NodeManager;

namespace z3 {

class Nnf
{
 public:
  Nnf(NodeManager* nm) : d_nm(nm) {}

  /** The negation normal form of the assertion n. */
  Node convert(TNode n);

 private:
  /**
   * The negation normal form of n under the polarity pol, where scope holds
   * the universally quantified variables that enclose n.
   */
  Node convertRec(TNode n, bool pol, const std::vector<Node>& scope);

  /** A fresh skolem of the type of v, applied to the variables in scope. */
  Node mkSkolem(TNode v, const std::vector<Node>& scope);

  NodeManager* d_nm;
  /**
   * The cache of the ground (quantifier-free) results, which do not depend
   * on the scope.
   */
  std::unordered_map<Node, Node> d_cache[2];
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__NNF_H */
