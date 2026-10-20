/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The elimination of the connectives the ported core does not internalize.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), and
 * recast in cvc5 style. Used only to prepare the assertions for the ported
 * core, see Z3AssertionPreparation.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__Z3__CONNECTIVE_NORMALIZER_H
#define CVC5__PREPROCESSING__Z3__CONNECTIVE_NORMALIZER_H

#include <unordered_map>

#include "expr/node.h"

namespace cvc5::internal {

class NodeManager;

namespace z3 {

/**
 * Rewrites the Boolean connectives Z3's rewriter eliminates before
 * internalization: (=> a b) becomes (or (not a) b), and (xor a b) becomes
 * (not (= a b)). The internalizer's notion of a "gate" is Z3's, which does
 * not cover these two, so they have to be gone by the time it runs.
 */
class ConnectiveNormalizer
{
 public:
  ConnectiveNormalizer(NodeManager* nm) : d_nm(nm) {}

  Node normalize(TNode n);

 private:
  NodeManager* d_nm;
  std::unordered_map<Node, Node> d_cache;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__Z3__CONNECTIVE_NORMALIZER_H */
