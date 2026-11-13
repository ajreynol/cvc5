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
 * Ported from Z3: src/smt/smt_checker.h, src/smt/smt_checker.cpp.
 * Z3 is Copyright (c) Microsoft Corporation and licensed under the MIT
 * License, see licenses/z3-LICENSE.
 *
 * The check is done without internalizing the instance: the body is evaluated
 * structurally, mapping its ground subterms to existing enodes and reading
 * off the current assignment. Instances that are already satisfied are then
 * never created, and instances that are already in conflict are promoted
 * ahead of the queue.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__CHECKER_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__CHECKER_H

#include <unordered_map>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

class EGraph;
class ENode;
class PropCore;

/**
 * Evaluates an instance body under bindings, against the assignment and the
 * E-graph of the core, without internalizing it.
 */
class Checker
{
 public:
  /** Make the checker over the E-graph egraph and the Boolean side prop. */
  Checker(EGraph& egraph, PropCore& prop);

  /** True if the body is already satisfied under the given bindings. */
  bool isSat(TNode n, size_t numBindings, ENode* const* bindings);

  /** True if the body is already falsified under the given bindings. */
  bool isUnsat(TNode n, size_t numBindings, ENode* const* bindings);

 private:
  /** True if n has the value isTrue under the given bindings. */
  bool run(TNode n, size_t numBindings, ENode* const* bindings, bool isTrue);
  /** True if every argument of a has the value isTrue. */
  bool allArgs(TNode a, size_t depth, bool isTrue);
  /** True if some argument of a has the value isTrue. */
  bool anyArg(TNode a, size_t depth, bool isTrue);
  /**
   * True if n, at the given depth of the body, is known to have the value
   * isTrue: by the assignment of n if it is relevant, else by the rule of
   * its connective, else by the assignment of an equal relevant enode.
   * False past the maximum depth.
   */
  bool checkCore(TNode n, size_t depth, bool isTrue);
  /** checkCore, cached for the current run. */
  bool check(TNode n, size_t depth, bool isTrue);
  /**
   * A relevant enode congruent to the application n, whose arguments are
   * mapped by getENodeEqTo, or null.
   */
  ENode* getENodeEqToCore(TNode n);
  /**
   * A relevant enode equal to n under the bindings, or null: the binding of
   * a variable, the enode of n, or one found by getENodeEqToCore (cached).
   */
  ENode* getENodeEqTo(TNode n);
  /**
   * True if n1 and n2 are known to be distinct: their roots are distinct
   * constants, or their equality is relevant and false.
   */
  bool isDiseq(ENode* n1, ENode* n2);

  /** The E-graph of the core. */
  EGraph& d_egraph;
  /** The Boolean side of the core, whose assignment and relevancy are read. */
  PropCore& d_prop;
  /** The results of check for each value (index 1 for true), per run. */
  std::unordered_map<Node, bool> d_isTrueCache[2];
  /** The results of getENodeEqTo for applications, per run. */
  std::unordered_map<Node, ENode*> d_toENodeCache;
  /** The number of bindings of the current run. */
  size_t d_numBindings;
  /** The bindings of the current run, indexed by variable index. */
  ENode* const* d_bindings;
};

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER__CHECKER_H */
