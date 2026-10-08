/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A cheap check of whether an instance is already satisfied, or already in
 * conflict, under the current assignment.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), files
 * src/smt/smt_checker.h and src/smt/smt_checker.cpp, recast in cvc5 style.
 *
 * The check is done without internalizing the instance: the body is evaluated
 * structurally, mapping its ground subterms to existing enodes and reading
 * off the current assignment. Instances that are already satisfied are then
 * never created, and instances that are already in conflict are promoted
 * ahead of the queue.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__CHECKER_H
#define CVC5__Z3__CHECKER_H

#include <unordered_map>

#include "expr/node.h"
#include "z3/types.h"

namespace cvc5::internal {
namespace z3 {

class SmtContext;

class Checker
{
 public:
  Checker(SmtContext& c);

  /** True if the body is already satisfied under the given bindings. */
  bool isSat(TNode n, size_t numBindings = 0, ENode* const* bindings = nullptr);

  /** True if the body is already falsified under the given bindings. */
  bool isUnsat(TNode n,
               size_t numBindings = 0,
               ENode* const* bindings = nullptr);

 private:
  bool allArgs(TNode a, size_t depth, bool isTrue);
  bool anyArg(TNode a, size_t depth, bool isTrue);
  bool checkCore(TNode n, size_t depth, bool isTrue);
  bool check(TNode n, size_t depth, bool isTrue);
  ENode* getENodeEqToCore(TNode n);
  ENode* getENodeEqTo(TNode n);

  SmtContext& d_context;
  std::unordered_map<Node, bool> d_isTrueCache[2];
  std::unordered_map<Node, ENode*> d_toENodeCache;
  size_t d_numBindings;
  ENode* const* d_bindings;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__CHECKER_H */
