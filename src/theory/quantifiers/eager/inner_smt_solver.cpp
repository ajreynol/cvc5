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
#include <set>
#include <unordered_set>

#include "theory/quantifiers/quantifiers_state.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

/**
 * The number of propagations the inner solver exports per round. Exporting a
 * propagation means adding an implication to the outer solver, which is not
 * free, so the number is bounded.
 */
static const size_t s_maxPropagationsPerRound = 8;
/**
 * The number of classes above which the search for outer disequalities, which
 * is quadratic, is skipped.
 */
static const size_t s_maxClassesForDiseqScan = 200;

InnerSmtSolver::InnerSmtSolver(Env& env, Trail& trail, QuantifiersState& qs)
    : EnvObj(env),
      d_trail(trail),
      d_qstate(qs),
      d_egraph(env),
      d_arith(env),
      d_roundCheckpoint(0)
{
  NodeManager* nm = nodeManager();
  d_trueTerm = d_egraph.addTerm(nm->mkConst(true));
  d_falseTerm = d_egraph.addTerm(nm->mkConst(false));
  // true and false are distinct, with no reason: the explanation of a conflict
  // that uses it does not have to mention it
  d_egraph.assertDiseq(d_trueTerm, d_falseTerm, Node::null());
  d_roundCheckpoint = d_egraph.checkpoint();
}

InnerSmtSolver::~InnerSmtSolver() {}

Node InnerSmtSolver::negate(TNode lit)
{
  return lit.getKind() == Kind::NOT ? Node(lit[0]) : lit.notNode();
}

size_t InnerSmtSolver::getAtom(TNode atom)
{
  std::map<Node, size_t>::const_iterator it = d_atomMap.find(atom);
  if (it != d_atomMap.end())
  {
    return it->second;
  }
  size_t id = d_atoms.size();
  d_atoms.push_back(Atom());
  Atom& a = d_atoms.back();
  a.d_node = atom;
  d_atomMap[atom] = id;
  // Give the atom a presence in the congruence closure, so that congruence
  // reasons about it. An equality is handled through its two sides; anything
  // else is a term that is merged with true or false when it is assigned.
  if (atom.getKind() == Kind::EQUAL && !atom[0].getType().isBoolean())
  {
    a.d_lhs = d_egraph.addTerm(atom[0]);
    a.d_rhs = d_egraph.addTerm(atom[1]);
  }
  else if (atom.getNumChildren() > 0 && atom.hasOperator() && !atom.isClosure())
  {
    a.d_term = d_egraph.addTerm(atom);
  }
  return id;
}

InnerSmtSolver::LitId InnerSmtSolver::getLit(TNode lit)
{
  if (lit.getKind() == Kind::NOT)
  {
    return mkLit(getAtom(lit[0]), true);
  }
  return mkLit(getAtom(lit), false);
}

Node InnerSmtSolver::getLitNode(LitId l) const
{
  Node atom = d_atoms[litAtom(l)].d_node;
  return litNeg(l) ? atom.notNode() : atom;
}

InnerSmtSolver::Value InnerSmtSolver::value(LitId l) const
{
  Value v = d_atoms[litAtom(l)].d_value;
  if (v == Value::UNDEF || !litNeg(l))
  {
    return v;
  }
  return v == Value::TRUE ? Value::FALSE : Value::TRUE;
}

void InnerSmtSolver::getClauseLits(TNode body, std::vector<LitId>& lits)
{
  // An instance body that is not a clause is not broken down: a conjunction or
  // an equivalence is taken as an opaque atom, which loses propagation but
  // stays sound. z3 internalizes the body fully instead.
  if (body.getKind() == Kind::OR)
  {
    for (const Node& d : body)
    {
      lits.push_back(getLit(d));
    }
    return;
  }
  lits.push_back(getLit(body));
}

void InnerSmtSolver::addClause(const std::vector<LitId>& lits, size_t instance)
{
  d_clauses.push_back(Clause{lits, instance});
  size_t idx = d_clauses.size() - 1;
  for (LitId l : lits)
  {
    std::vector<size_t>& occ = d_atoms[litAtom(l)].d_occurs;
    if (occ.empty() || occ.back() != idx)
    {
      occ.push_back(idx);
    }
  }
}

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
  inst.d_numClauses = d_clauses.size();
  inst.d_numAtoms = d_atoms.size();
  size_t n = d_instances.size();
  d_instances.push_back(inst);
  d_stats.d_numInstances++;
  Trace("eager-inner") << "InnerSmtSolver: add instance " << lemma
                       << ", generation " << generation << std::endl;
  // The clause of the instance. Its first literal is (not q), which is false
  // because q is asserted in the outer context, so the clause behaves as the
  // body does.
  std::vector<LitId> lits;
  getClauseLits(lemma, lits);
  addClause(lits, n);
  // The terms of the instance are now part of the congruence closure, so a
  // round must not undo them.
  d_roundCheckpoint = d_egraph.checkpoint();
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
  // the clauses and atoms of the retracted instances
  for (size_t c = first.d_numClauses, nc = d_clauses.size(); c < nc; c++)
  {
    for (LitId l : d_clauses[c].d_lits)
    {
      std::vector<size_t>& occ = d_atoms[litAtom(l)].d_occurs;
      while (!occ.empty() && occ.back() >= first.d_numClauses)
      {
        occ.pop_back();
      }
    }
  }
  d_clauses.resize(first.d_numClauses);
  for (size_t a = first.d_numAtoms, na = d_atoms.size(); a < na; a++)
  {
    d_atomMap.erase(d_atoms[a].d_node);
  }
  d_atoms.resize(first.d_numAtoms);
  d_egraph.restoreTo(first.d_egraphCheckpoint);
  d_arith.restoreTo(first.d_arithCheckpoint);
  d_stats.d_numRetracted += d_instances.size() - n;
  d_instances.resize(n);
  d_roundCheckpoint = d_egraph.checkpoint();
}

void InnerSmtSolver::syncOuter()
{
  // The outer assignment is read rather than pushed: the atoms the inner solver
  // cares about are known, so their values can be asked for. A literal taken
  // this way is a root of the explanation of whatever follows from it.
  Valuation& val = d_qstate.getValuation();
  for (size_t i = 0, natoms = d_atoms.size(); i < natoms; i++)
  {
    if (d_atoms[i].d_value != Value::UNDEF)
    {
      continue;
    }
    bool v = false;
    if (!val.hasSatValue(d_atoms[i].d_node, v))
    {
      continue;
    }
    if (!assign(mkLit(i, !v), ReasonKind::OUTER, 0, {}))
    {
      return;
    }
  }
}

bool InnerSmtSolver::assignOuter(TNode atom, bool pol)
{
  LitId l = mkLit(getAtom(atom), !pol);
  return assign(l, ReasonKind::OUTER, 0, {});
}

void InnerSmtSolver::syncOuterEqualities()
{
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  if (ee == nullptr)
  {
    return;
  }
  // group the terms of this solver by their class in the master equality engine
  std::map<Node, std::vector<Node>> byRep;
  for (InnerEGraph::TermId t = 0, nterms = d_egraph.getNumTerms(); t < nterms;
       t++)
  {
    Node n = d_egraph.getNode(t);
    if (n.getType().isBoolean() || !ee->hasTerm(n))
    {
      continue;
    }
    byRep[d_qstate.getRepresentative(n)].push_back(n);
  }
  Trace("eager-inner-debug")
      << "  outer: " << d_egraph.getNumTerms() << " terms in " << byRep.size()
      << " classes" << std::endl;
  for (const std::pair<const Node, std::vector<Node>>& g : byRep)
  {
    for (size_t i = 1, nts = g.second.size(); i < nts; i++)
    {
      if (!assignOuter(g.second[0].eqNode(g.second[i]), true))
      {
        return;
      }
    }
  }
  // TODO: this is quadratic in the number of classes; z3 does not need it at
  // all, since its instances live in the solver that owns the disequalities.
  if (byRep.size() > s_maxClassesForDiseqScan)
  {
    Trace("eager-inner") << "InnerSmtSolver: skipping the disequality scan, "
                         << byRep.size() << " classes" << std::endl;
    return;
  }
  for (std::map<Node, std::vector<Node>>::const_iterator i1 = byRep.begin();
       i1 != byRep.end();
       ++i1)
  {
    std::map<Node, std::vector<Node>>::const_iterator i2 = i1;
    for (++i2; i2 != byRep.end(); ++i2)
    {
      if (i1->second[0].getType() != i2->second[0].getType())
      {
        continue;
      }
      if (!d_qstate.areDisequal(i1->first, i2->first))
      {
        continue;
      }
      if (!assignOuter(i1->second[0].eqNode(i2->second[0]), false))
      {
        return;
      }
    }
  }
}

bool InnerSmtSolver::assign(LitId l,
                            ReasonKind kind,
                            size_t clause,
                            std::vector<LitId> exp)
{
  Value v = value(l);
  if (v == Value::TRUE)
  {
    return true;
  }
  if (v == Value::FALSE)
  {
    // l is implied but its negation is already assigned
    d_conflictExp.clear();
    d_conflictExp.push_back(litNot(l));
    if (kind == ReasonKind::CLAUSE)
    {
      for (LitId cl : d_clauses[clause].d_lits)
      {
        if (cl != l)
        {
          d_conflictExp.push_back(litNot(cl));
        }
      }
      // the instance of the clause is part of the explanation, which
      // collectRoots picks up from the clause of the implied literal; add the
      // literal itself so that its clause is visited
      d_conflictExp.push_back(l);
      d_assignTrail.push_back(Assignment{l, kind, clause, {}});
    }
    else
    {
      for (LitId e : exp)
      {
        d_conflictExp.push_back(e);
      }
    }
    return false;
  }
  d_atoms[litAtom(l)].d_value = litNeg(l) ? Value::FALSE : Value::TRUE;
  d_assignTrail.push_back(Assignment{l, kind, clause, exp});
  d_queue.push_back(l);
  d_stats.d_numAssignments++;
  Trace("eager-inner-debug") << "  assign " << getLitNode(l) << std::endl;
  return assertToTheory(l);
}

bool InnerSmtSolver::assertToTheory(LitId l)
{
  const Atom& a = d_atoms[litAtom(l)];
  bool pol = !litNeg(l);
  Node lit = getLitNode(l);
  bool ok = true;
  if (a.d_lhs != InnerEGraph::undefinedTerm)
  {
    ok = pol ? d_egraph.assertEq(a.d_lhs, a.d_rhs, lit)
             : d_egraph.assertDiseq(a.d_lhs, a.d_rhs, lit);
  }
  else if (a.d_term != InnerEGraph::undefinedTerm)
  {
    // a predicate application: congruence over it is obtained by merging it
    // with true or false
    ok = d_egraph.assertEq(a.d_term, pol ? d_trueTerm : d_falseTerm, lit);
  }
  if (ok)
  {
    return true;
  }
  // the congruence closure gives the explanation as the literals that were
  // asserted to it
  d_conflictExp.clear();
  for (const Node& e : d_egraph.getConflict())
  {
    std::map<Node, size_t>::const_iterator it =
        d_atomMap.find(e.getKind() == Kind::NOT ? e[0] : e);
    Assert(it != d_atomMap.end());
    d_conflictExp.push_back(mkLit(it->second, e.getKind() == Kind::NOT));
  }
  return false;
}

bool InnerSmtSolver::propagate()
{
  for (;;)
  {
    while (!d_queue.empty())
    {
      LitId l = d_queue.back();
      d_queue.pop_back();
      // the clauses in which l is false
      LitId nl = litNot(l);
      const std::vector<size_t> occ = d_atoms[litAtom(nl)].d_occurs;
      for (size_t c : occ)
      {
        if (c >= d_clauses.size())
        {
          continue;
        }
        const Clause& cl = d_clauses[c];
        LitId unassigned = undefinedLit;
        bool satisfied = false;
        size_t numUnassigned = 0;
        for (LitId cli : cl.d_lits)
        {
          Value v = value(cli);
          if (v == Value::TRUE)
          {
            satisfied = true;
            break;
          }
          if (v == Value::UNDEF)
          {
            unassigned = cli;
            numUnassigned++;
            if (numUnassigned > 1)
            {
              break;
            }
          }
        }
        if (satisfied || numUnassigned > 1)
        {
          continue;
        }
        if (numUnassigned == 0)
        {
          // every literal is false
          d_conflictExp.clear();
          for (LitId cli : cl.d_lits)
          {
            d_conflictExp.push_back(litNot(cli));
          }
          // the instance of the clause itself is part of the explanation
          d_conflictClause = c;
          return false;
        }
        if (!assign(unassigned, ReasonKind::CLAUSE, c, {}))
        {
          return false;
        }
      }
    }
    bool progress = false;
    if (!theoryPropagate(progress))
    {
      return false;
    }
    if (!progress)
    {
      return true;
    }
  }
}

bool InnerSmtSolver::theoryPropagate(bool& progress)
{
  // TODO: z3 finds the atoms a merge implies through the congruence table; we
  // scan the unassigned atoms, which is fine while the inner problem is small.
  for (size_t i = 0, natoms = d_atoms.size(); i < natoms; i++)
  {
    Atom& a = d_atoms[i];
    if (a.d_value != Value::UNDEF)
    {
      continue;
    }
    bool implied = false;
    bool pol = true;
    if (a.d_lhs != InnerEGraph::undefinedTerm)
    {
      if (d_egraph.areEqual(a.d_lhs, a.d_rhs))
      {
        implied = true;
        pol = true;
      }
    }
    else if (a.d_term != InnerEGraph::undefinedTerm)
    {
      if (d_egraph.areEqual(a.d_term, d_trueTerm))
      {
        implied = true;
        pol = true;
      }
      else if (d_egraph.areEqual(a.d_term, d_falseTerm))
      {
        implied = true;
        pol = false;
      }
    }
    if (!implied)
    {
      continue;
    }
    std::vector<Node> exp;
    if (a.d_lhs != InnerEGraph::undefinedTerm)
    {
      d_egraph.explain(a.d_lhs, a.d_rhs, exp);
    }
    else
    {
      d_egraph.explain(a.d_term, pol ? d_trueTerm : d_falseTerm, exp);
    }
    std::vector<LitId> expLits;
    for (const Node& e : exp)
    {
      std::map<Node, size_t>::const_iterator it =
          d_atomMap.find(e.getKind() == Kind::NOT ? e[0] : e);
      Assert(it != d_atomMap.end());
      expLits.push_back(mkLit(it->second, e.getKind() == Kind::NOT));
    }
    progress = true;
    if (!assign(mkLit(i, !pol), ReasonKind::THEORY, 0, expLits))
    {
      return false;
    }
  }
  return true;
}

void InnerSmtSolver::resetRound()
{
  for (const Assignment& a : d_assignTrail)
  {
    d_atoms[litAtom(a.d_lit)].d_value = Value::UNDEF;
  }
  d_assignTrail.clear();
  d_queue.clear();
  d_conflictExp.clear();
  d_egraph.restoreTo(d_roundCheckpoint);
}

void InnerSmtSolver::collectRoots(LitId l,
                                  std::set<Node>& outerLits,
                                  std::set<size_t>& instances,
                                  std::unordered_set<LitId>& seen) const
{
  std::vector<LitId> todo{l};
  while (!todo.empty())
  {
    LitId curr = todo.back();
    todo.pop_back();
    if (!seen.insert(curr).second)
    {
      continue;
    }
    // find how curr was assigned
    const Assignment* asgn = nullptr;
    for (size_t i = d_assignTrail.size(); i-- > 0;)
    {
      if (d_assignTrail[i].d_lit == curr)
      {
        asgn = &d_assignTrail[i];
        break;
      }
    }
    if (asgn == nullptr)
    {
      // not assigned by us, so it is as good as an outer fact
      outerLits.insert(getLitNode(curr));
      continue;
    }
    switch (asgn->d_kind)
    {
      case ReasonKind::OUTER: outerLits.insert(getLitNode(curr)); break;
      case ReasonKind::CLAUSE:
      {
        const Clause& cl = d_clauses[asgn->d_clause];
        if (cl.d_instance < d_instances.size())
        {
          instances.insert(cl.d_instance);
        }
        for (LitId cli : cl.d_lits)
        {
          if (cli != curr)
          {
            todo.push_back(litNot(cli));
          }
        }
      }
      break;
      case ReasonKind::THEORY:
        for (LitId e : asgn->d_exp)
        {
          todo.push_back(e);
        }
        break;
    }
  }
}

void InnerSmtSolver::noteUsedInstances(const std::set<size_t>& instances)
{
  for (size_t i : instances)
  {
    d_usedInstantiations.emplace_back(d_instances[i].d_quant,
                                      d_instances[i].d_terms);
  }
}

Node InnerSmtSolver::mkConflict(const std::vector<LitId>& exp)
{
  std::set<Node> outerLits;
  std::set<size_t> instances;
  std::unordered_set<LitId> seen;
  for (LitId l : exp)
  {
    if (l != undefinedLit)
    {
      collectRoots(l, outerLits, instances, seen);
    }
  }
  if (d_conflictClause < d_clauses.size()
      && d_clauses[d_conflictClause].d_instance < d_instances.size())
  {
    instances.insert(d_clauses[d_conflictClause].d_instance);
  }
  std::set<Node> disjunctSet;
  for (const Node& l : outerLits)
  {
    disjunctSet.insert(negate(l));
  }
  for (size_t i : instances)
  {
    disjunctSet.insert(d_instances[i].d_quant.notNode());
  }
  std::vector<Node> disjuncts(disjunctSet.begin(), disjunctSet.end());
  if (disjuncts.empty())
  {
    // nothing the outer solver can act on
    return Node::null();
  }
  noteUsedInstances(instances);
  NodeManager* nm = nodeManager();
  return disjuncts.size() == 1 ? disjuncts[0] : nm->mkNode(Kind::OR, disjuncts);
}

bool InnerSmtSolver::check()
{
  d_stats.d_numChecks++;
  d_conflict = Node::null();
  d_usedInstantiations.clear();
  d_conflictClause = d_clauses.size();
  if (d_clauses.empty())
  {
    return true;
  }
  resetRound();
  syncOuter();
  if (d_conflictExp.empty())
  {
    syncOuterEqualities();
  }
  bool ok = d_conflictExp.empty() && propagate();
  if (!ok)
  {
    d_conflict = mkConflict(d_conflictExp);
    if (!d_conflict.isNull())
    {
      d_stats.d_numConflicts++;
      Trace("eager-inner") << "InnerSmtSolver: conflict " << d_conflict
                           << std::endl;
      resetRound();
      return false;
    }
  }
  // Export a bounded number of the literals we derived that the outer solver
  // has a variable for but no value.
  Valuation& val = d_qstate.getValuation();
  for (const Assignment& a : d_assignTrail)
  {
    if (d_propagations.size() >= s_maxPropagationsPerRound)
    {
      break;
    }
    if (a.d_kind == ReasonKind::OUTER)
    {
      continue;
    }
    Node lit = getLitNode(a.d_lit);
    Node atom = d_atoms[litAtom(a.d_lit)].d_node;
    if (!val.isSatLiteral(atom) || val.hasSatValue(atom))
    {
      continue;
    }
    std::set<Node> outerLits;
    std::set<size_t> instances;
    std::unordered_set<LitId> seen;
    collectRoots(a.d_lit, outerLits, instances, seen);
    std::vector<Node> conj(outerLits.begin(), outerLits.end());
    for (size_t i : instances)
    {
      conj.push_back(d_instances[i].d_quant);
    }
    if (conj.empty())
    {
      continue;
    }
    NodeManager* nm = nodeManager();
    Node exp = conj.size() == 1 ? conj[0] : nm->mkNode(Kind::AND, conj);
    d_propagations.emplace_back(lit, exp);
    noteUsedInstances(instances);
    d_stats.d_numPropagations++;
  }
  resetRound();
  return true;
}

void InnerSmtSolver::debugPrint(std::ostream& out) const
{
  out << "inner-smt-solver: " << d_instances.size() << " instances, "
      << d_clauses.size() << " clauses, " << d_atoms.size() << " atoms"
      << std::endl;
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
