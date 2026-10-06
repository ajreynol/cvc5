/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The inner SMT solver, which owns the instances eager E-matching produces.
 */

#include "theory/quantifiers/eager/inner_smt_solver.h"

#include <ostream>

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

InnerSmtSolver::InnerSmtSolver(Env& env, Trail& trail)
    : EnvObj(env), d_trail(trail), d_egraph(env), d_arith(env)
{
}

InnerSmtSolver::~InnerSmtSolver() {}

void InnerSmtSolver::addInstance(TNode q,
                                 const std::vector<Node>& terms,
                                 TNode lemma,
                                 uint32_t generation)
{
  Instance inst;
  inst.d_quant = q;
  inst.d_terms = terms;
  inst.d_lemma = lemma;
  inst.d_generation = generation;
  inst.d_egraphCheckpoint = d_egraph.checkpoint();
  inst.d_arithCheckpoint = d_arith.checkpoint();
  size_t n = d_instances.size();
  d_instances.push_back(inst);
  d_stats.d_numInstances++;
  Trace("eager-inner") << "InnerSmtSolver: add instance " << lemma
                       << ", generation " << generation << std::endl;
  // the terms of the instance become part of the congruence closure
  d_egraph.addTerm(lemma);
  // instances are dropped when the scope they were added at is popped, as in
  // z3's qi_queue::pop_scope
  d_trail.onPop([this, n]() { retractInstancesFrom(n); });
}

void InnerSmtSolver::retractInstancesFrom(size_t n)
{
  if (d_instances.size() <= n)
  {
    return;
  }
  const Instance& first = d_instances[n];
  d_egraph.restoreTo(first.d_egraphCheckpoint);
  d_arith.restoreTo(first.d_arithCheckpoint);
  d_stats.d_numRetracted += d_instances.size() - n;
  d_instances.resize(n);
}

void InnerSmtSolver::notifyAssertedLit(TNode lit)
{
  Trace("eager-inner") << "InnerSmtSolver: assert " << lit << std::endl;
  size_t n = d_assignment.size();
  d_assignment.push_back(lit);
  d_trail.onPop([this, n]() { d_assignment.resize(n); });
  // TODO: dispatch the literal to the congruence closure or the arithmetic
  // solver. See README.md section 9, step 6.
}

bool InnerSmtSolver::check()
{
  d_stats.d_numChecks++;
  d_conflict = Node::null();
  // TODO: the Boolean search over the instance clauses, with the congruence
  // closure and the arithmetic solver as the theory. The clauses are in
  // d_instances, the outer assignment in d_assignment. On a conflict, set
  // d_conflict to the disjunction of (not q) for the quantified formulas whose
  // instances were used and the negations of the outer literals used; that
  // clause is entailed by the assertions regardless of how it was found. See
  // README.md section 9, step 6.
  return true;
}

void InnerSmtSolver::debugPrint(std::ostream& out) const
{
  out << "inner-smt-solver: " << d_instances.size() << " instances, "
      << d_assignment.size() << " replayed literals" << std::endl;
  for (const Instance& i : d_instances)
  {
    out << "  " << i.d_lemma << std::endl;
  }
  d_egraph.debugPrint(out);
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
