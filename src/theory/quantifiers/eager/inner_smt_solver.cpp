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

#include <algorithm>
#include <ostream>

#include "options/quantifiers_options.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_state.h"

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

InnerSmtSolver::InnerSmtSolver(Env& env,
                               Trail& trail,
                               QuantifiersState& qs,
                               EGraph& mirror)
    : EnvObj(env),
      d_trail(trail),
      d_qstate(qs),
      d_mirror(mirror),
      d_inst(nullptr),
      d_feedback(options().quantifiers.eagerInstFeedback),
      d_egraph(env),
      d_arith(env),
      d_clauseHead(0),
      d_conflictClause(0),
      d_outerFactHead(0),
      d_candidateHead(0),
      d_touchedHead(0),
      d_exportHead(0),
      d_savedScope(0),
      d_decisionHint(0),
      d_propagateOut(options().quantifiers.eagerInstPropagate),
      d_budget(options().quantifiers.eagerInstInnerBudget)
{
  NodeManager* nm = nodeManager();
  d_trueTerm = d_egraph.addTerm(nm->mkConst(true));
  d_falseTerm = d_egraph.addTerm(nm->mkConst(false));
  // true and false are distinct, with no reason: the explanation of a conflict
  // that uses it does not have to mention it
  d_egraph.assertDiseq(d_trueTerm, d_falseTerm, Node::null());
  d_egraph.setListener(this);
}

InnerSmtSolver::~InnerSmtSolver() {}

Node InnerSmtSolver::negate(TNode lit)
{
  return lit.getKind() == Kind::NOT ? Node(lit[0]) : lit.notNode();
}

//------------------------------------------------------------- state saving

InnerSmtSolver::Checkpoint InnerSmtSolver::mkCheckpoint() const
{
  return Checkpoint{d_egraph.checkpoint(),
                    d_arith.checkpoint(),
                    d_instances.size(),
                    d_clauses.size(),
                    d_atoms.size(),
                    d_assignTrail.size(),
                    d_clauseHead,
                    d_outerFacts.size(),
                    d_outerFactHead,
                    d_candidates.size(),
                    d_candidateHead,
                    d_touched.size(),
                    d_touchedHead,
                    d_exportHead};
}

void InnerSmtSolver::restoreTo(const Checkpoint& c)
{
  // the assignment
  for (size_t i = d_assignTrail.size(); i-- > c.d_assign;)
  {
    Atom& a = d_atoms[litAtom(d_assignTrail[i].d_lit)];
    a.d_value = Value::UNDEF;
    a.d_trailIndex = noIndex;
  }
  d_assignTrail.resize(c.d_assign);
  d_queue.clear();
  d_conflictExp.clear();
  // the clauses
  for (size_t ci = c.d_clauses, nc = d_clauses.size(); ci < nc; ci++)
  {
    for (LitId l : d_clauses[ci].d_lits)
    {
      std::vector<size_t>& occ = d_atoms[litAtom(l)].d_occurs;
      while (!occ.empty() && occ.back() >= c.d_clauses)
      {
        occ.pop_back();
      }
    }
  }
  d_clauses.resize(c.d_clauses);
  // the atoms, which are at the end of the watch lists they are on
  for (size_t ai = d_atoms.size(); ai-- > c.d_atoms;)
  {
    const Atom& a = d_atoms[ai];
    for (TermId t : {a.d_term, a.d_lhs, a.d_rhs})
    {
      if (t != InnerEGraph::undefinedTerm && t < d_watches.size())
      {
        std::vector<size_t>& w = d_watches[t];
        while (!w.empty() && w.back() >= c.d_atoms)
        {
          w.pop_back();
        }
      }
    }
    d_atomMap.erase(a.d_node);
  }
  d_atoms.resize(c.d_atoms);
  // the theories
  d_egraph.restoreTo(c.d_egraph);
  d_arith.restoreTo(c.d_arith);
  if (d_watches.size() > d_egraph.getNumTerms())
  {
    d_watches.resize(d_egraph.getNumTerms());
  }
  d_stats.d_numRetracted += d_instances.size() - c.d_instances;
  d_instances.resize(c.d_instances);
  // the work lists
  d_clauseHead = c.d_clauseHead;
  d_outerFacts.resize(c.d_outerFacts);
  d_outerFactHead = c.d_outerFactHead;
  d_candidates.resize(c.d_candidates);
  d_candidateHead = c.d_candidateHead;
  d_touched.resize(c.d_touched);
  d_touchedHead = c.d_touchedHead;
  // what was exported before c stays exported
  d_exportHead = std::min(d_exportHead, c.d_assign);
}

void InnerSmtSolver::ensureScopeSaved()
{
  uint32_t n = static_cast<uint32_t>(d_trail.getNumScopes());
  if (n == 0 || d_savedScope == n)
  {
    // nothing to undo at the outermost scope, or saved already
    return;
  }
  d_trail.restore(&d_savedScope);
  d_savedScope = n;
  Checkpoint c = mkCheckpoint();
  d_trail.onPop([this, c]() { restoreTo(c); });
}

//--------------------------------------------------------- atoms, clauses

size_t InnerSmtSolver::getAtom(TNode atom)
{
  std::map<Node, size_t>::const_iterator it = d_atomMap.find(atom);
  if (it != d_atomMap.end())
  {
    return it->second;
  }
  size_t id = d_atoms.size();
  d_atoms.push_back(Atom());
  d_atoms.back().d_node = atom;
  d_atomMap[atom] = id;
  // Give the atom a presence in the congruence closure, so that congruence
  // reasons about it. An equality is handled through its two sides; anything
  // else is a term that is merged with true or false when it is assigned.
  if (atom.getKind() == Kind::EQUAL && !atom[0].getType().isBoolean())
  {
    TermId lhs = d_egraph.addTerm(atom[0]);
    TermId rhs = d_egraph.addTerm(atom[1]);
    d_atoms[id].d_lhs = lhs;
    d_atoms[id].d_rhs = rhs;
    addWatch(lhs, id);
    addWatch(rhs, id);
  }
  else if (atom.getNumChildren() > 0 && atom.hasOperator() && !atom.isClosure()
           && !needsDefinition(atom))
  {
    TermId t = d_egraph.addTerm(atom);
    d_atoms[id].d_term = t;
    addWatch(t, id);
  }
  // the congruence closure may imply it already
  d_candidates.push_back(id);
  return id;
}

void InnerSmtSolver::addWatch(TermId t, size_t atom)
{
  if (d_watches.size() <= t)
  {
    d_watches.resize(d_egraph.getNumTerms());
  }
  d_watches[t].push_back(atom);
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

bool InnerSmtSolver::needsDefinition(TNode f)
{
  switch (f.getKind())
  {
    case Kind::AND:
    case Kind::OR:
    case Kind::IMPLIES:
    case Kind::XOR: return true;
    case Kind::ITE: return f.getType().isBoolean();
    case Kind::EQUAL: return f[0].getType().isBoolean();
    default: return false;
  }
}

InnerSmtSolver::LitId InnerSmtSolver::litFor(TNode f)
{
  if (f.getKind() == Kind::NOT)
  {
    return litNot(litFor(f[0]));
  }
  return mkLit(getAtom(f), false);
}

void InnerSmtSolver::defineAtom(TNode f, size_t instance)
{
  size_t a = getAtom(f);
  if (d_atoms[a].d_defined)
  {
    return;
  }
  d_atoms[a].d_defined = true;
  LitId x = mkLit(a, false);
  switch (f.getKind())
  {
    case Kind::AND:
    {
      // x -> each child, and all children -> x
      std::vector<LitId> all{x};
      for (const Node& c : f)
      {
        LitId l = litFor(c);
        addClause({litNot(x), l}, instance);
        all.push_back(litNot(l));
      }
      addClause(all, instance);
    }
    break;
    case Kind::OR:
    {
      // x -> some child, and each child -> x
      std::vector<LitId> all{litNot(x)};
      for (const Node& c : f)
      {
        LitId l = litFor(c);
        addClause({x, litNot(l)}, instance);
        all.push_back(l);
      }
      addClause(all, instance);
    }
    break;
    case Kind::IMPLIES:
    {
      LitId a0 = litFor(f[0]);
      LitId b0 = litFor(f[1]);
      addClause({litNot(x), litNot(a0), b0}, instance);
      addClause({x, a0}, instance);
      addClause({x, litNot(b0)}, instance);
    }
    break;
    case Kind::EQUAL:
    case Kind::XOR:
    {
      // x <-> (a = b) for EQUAL, x <-> (a != b) for XOR
      LitId a0 = litFor(f[0]);
      LitId b0 = litFor(f[1]);
      LitId e = f.getKind() == Kind::XOR ? litNot(x) : x;
      addClause({litNot(e), litNot(a0), b0}, instance);
      addClause({litNot(e), a0, litNot(b0)}, instance);
      addClause({e, a0, b0}, instance);
      addClause({e, litNot(a0), litNot(b0)}, instance);
    }
    break;
    case Kind::ITE:
    {
      LitId c0 = litFor(f[0]);
      LitId t0 = litFor(f[1]);
      LitId e0 = litFor(f[2]);
      addClause({litNot(c0), litNot(x), t0}, instance);
      addClause({litNot(c0), x, litNot(t0)}, instance);
      addClause({c0, litNot(x), e0}, instance);
      addClause({c0, x, litNot(e0)}, instance);
    }
    break;
    default: Unreachable(); break;
  }
}

InnerSmtSolver::LitId InnerSmtSolver::encode(TNode f, size_t instance)
{
  // Define the connectives of f bottom up. The traversal is iterative because
  // an instance body can be deep.
  std::vector<std::pair<TNode, bool>> visit{{f, false}};
  std::unordered_set<TNode> done;
  std::vector<TNode> order;
  while (!visit.empty())
  {
    TNode c = visit.back().first;
    if (done.find(c) != done.end())
    {
      visit.pop_back();
      continue;
    }
    if (!visit.back().second)
    {
      visit.back().second = true;
      if (c.getKind() == Kind::NOT)
      {
        visit.push_back({c[0], false});
      }
      else if (needsDefinition(c))
      {
        for (const Node& cc : c)
        {
          visit.push_back({cc, false});
        }
      }
      continue;
    }
    visit.pop_back();
    done.insert(c);
    order.push_back(c);
  }
  for (TNode c : order)
  {
    if (needsDefinition(c))
    {
      defineAtom(c, instance);
    }
  }
  return litFor(f);
}

void InnerSmtSolver::addFormula(TNode f, size_t instance)
{
  // A top level conjunction is asserted conjunct by conjunct, and a top level
  // disjunction becomes one clause, so that neither needs a definition.
  if (f.getKind() == Kind::AND)
  {
    for (const Node& c : f)
    {
      addFormula(c, instance);
    }
    return;
  }
  if (f.getKind() == Kind::OR)
  {
    std::vector<LitId> lits;
    for (const Node& c : f)
    {
      lits.push_back(encode(c, instance));
    }
    addClause(lits, instance);
    return;
  }
  addClause({encode(f, instance)}, instance);
}

void InnerSmtSolver::addClause(const std::vector<LitId>& lits, size_t instance)
{
  // The encoding of a formula can produce a clause with a repeated or opposite
  // pair of literals, which is either redundant or a tautology.
  std::vector<LitId> cl;
  for (LitId l : lits)
  {
    if (std::find(cl.begin(), cl.end(), litNot(l)) != cl.end())
    {
      return;
    }
    if (std::find(cl.begin(), cl.end(), l) == cl.end())
    {
      cl.push_back(l);
    }
  }
  d_clauses.push_back(Clause{cl, instance});
  size_t idx = d_clauses.size() - 1;
  for (LitId l : cl)
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
  if (d_inst != nullptr && d_inst->existsInstantiation(q, terms))
  {
    // cvc5 already has this instantiation, so its body is already asserted in
    // the outer solver and holding a copy here would only lead to the same
    // conflict being rederived after every backtrack.
    d_stats.d_numAlreadyKnown++;
    return;
  }
  if (d_feedback)
  {
    // the terms of this instance become candidates for further matching
    feedMirror(lemma);
  }
  ensureScopeSaved();
  size_t numTerms = d_egraph.getNumTerms();
  size_t n = d_instances.size();
  d_instances.push_back(
      Instance{q, terms, lemma, generation, d_clauses.size()});
  d_stats.d_numInstances++;
  Trace("eager-inner") << "InnerSmtSolver: add instance " << lemma
                       << ", generation " << generation << std::endl;
  // The clause of the instance. Its first literal is (not q), which is false
  // because q is asserted in the outer context, so the clause behaves as the
  // body does. It is examined at the next round. Like the rest of the state,
  // it is dropped when the current scope is popped, as in z3's
  // qi_queue::pop_scope.
  addFormula(lemma, n);
  // the new terms that the outer solver knows about
  for (TermId t = numTerms, nterms = d_egraph.getNumTerms(); t < nterms; t++)
  {
    if (d_egraph.isBoolean(t))
    {
      continue;
    }
    ENode* e = d_mirror.getENode(d_egraph.getNode(t));
    if (e != nullptr)
    {
      linkToOuter(t, e->getRoot());
    }
  }
}

//---------------------------------------------- the link to the outer solver

InnerSmtSolver::TermId InnerSmtSolver::getAnchor(ENode* r) const
{
  std::unordered_map<ENode*, TermId>::const_iterator it = d_anchors.find(r);
  return it == d_anchors.end() ? InnerEGraph::undefinedTerm : it->second;
}

void InnerSmtSolver::setAnchor(ENode* r, TermId t)
{
  TermId old = getAnchor(r);
  d_anchors[r] = t;
  if (d_trail.getNumScopes() > 0)
  {
    d_trail.onPop([this, r, old]() {
      if (old == InnerEGraph::undefinedTerm)
      {
        d_anchors.erase(r);
      }
      else
      {
        d_anchors[r] = old;
      }
    });
  }
}

void InnerSmtSolver::linkToOuter(TermId t, ENode* r)
{
  TermId a = getAnchor(r);
  if (a == InnerEGraph::undefinedTerm)
  {
    setAnchor(r, t);
  }
  else if (a != t)
  {
    addOuterFact(a, t, true);
  }
}

void InnerSmtSolver::feedMirror(TNode f)
{
  std::vector<TNode> visit{f};
  std::unordered_set<TNode> visited;
  while (!visit.empty())
  {
    TNode n = visit.back();
    visit.pop_back();
    if (!visited.insert(n).second || n.isClosure())
    {
      continue;
    }
    Kind k = n.getKind();
    bool connective = k == Kind::NOT || k == Kind::AND || k == Kind::OR
                      || k == Kind::IMPLIES || k == Kind::XOR
                      || k == Kind::DISTINCT || k == Kind::EQUAL
                      || (k == Kind::ITE && n.getType().isBoolean());
    if (!connective && n.getNumChildren() > 0 && n.hasOperator())
    {
      // a term the matcher can match on; addTerm covers its arguments too
      if (d_mirror.addTerm(n) != nullptr)
      {
        d_stats.d_numFedTerms++;
      }
      continue;
    }
    for (const Node& nc : n)
    {
      visit.push_back(nc);
    }
  }
}

void InnerSmtSolver::addOuterFact(TermId a, TermId b, bool pol)
{
  d_outerFacts.push_back(OuterFact{a, b, pol});
}

void InnerSmtSolver::notifyNewENode(ENode* e)
{
  TermId t = d_egraph.getTerm(e->getNode());
  if (t == InnerEGraph::undefinedTerm || d_egraph.isBoolean(t))
  {
    return;
  }
  ensureScopeSaved();
  linkToOuter(t, e->getRoot());
}

void InnerSmtSolver::notifyPreMerge(ENode* r1, ENode* r2)
{
  // r1 is absorbed into r2, so r2 inherits the anchor of r1 if it has none,
  // and otherwise the two anchors are now equal
  TermId a1 = getAnchor(r1);
  if (a1 == InnerEGraph::undefinedTerm)
  {
    return;
  }
  ensureScopeSaved();
  TermId a2 = getAnchor(r2);
  if (a2 == InnerEGraph::undefinedTerm)
  {
    setAnchor(r2, a1);
  }
  else
  {
    addOuterFact(a1, a2, true);
  }
}

void InnerSmtSolver::notifyDiseq(ENode* e1, ENode* e2)
{
  // A disequality between classes that contain none of our terms is not
  // recorded. If we later have terms in both and merge them, the merge is
  // checked against the outer disequalities (checkTouchedClasses).
  TermId a1 = getAnchor(e1->getRoot());
  TermId a2 = getAnchor(e2->getRoot());
  if (a1 == InnerEGraph::undefinedTerm || a2 == InnerEGraph::undefinedTerm)
  {
    return;
  }
  ensureScopeSaved();
  addOuterFact(a1, a2, false);
}

void InnerSmtSolver::notifyMerge(size_t a, size_t b)
{
  // the class of b is checked against the outer disequalities later
  d_touched.push_back(b);
  // The atoms the merge may imply are those watching a term of one of the two
  // classes: an equality has a side in each, and a predicate application is
  // implied when its class meets that of true or false. So it is enough to
  // visit the class that does not contain true or false, which is a unless a
  // contains one of them.
  TermId s = a;
  TermId rt = d_egraph.find(d_trueTerm);
  TermId rf = d_egraph.find(d_falseTerm);
  if (a == rt || a == rf)
  {
    s = b;
  }
  TermId t = s;
  do
  {
    if (t < d_watches.size())
    {
      for (size_t atom : d_watches[t])
      {
        d_candidates.push_back(atom);
      }
    }
    t = d_egraph.getNext(t);
  } while (t != s);
}

bool InnerSmtSolver::syncOuter()
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
      return false;
    }
  }
  return true;
}

bool InnerSmtSolver::assignOuter(TNode atom, bool pol)
{
  LitId l = mkLit(getAtom(atom), !pol);
  return assign(l, ReasonKind::OUTER, 0, {});
}

bool InnerSmtSolver::processOuterFacts()
{
  // Each fact holds in the outer context, whatever the reason the master
  // equality engine had for it, so each is sound as a root of an explanation.
  while (d_outerFactHead < d_outerFacts.size())
  {
    OuterFact f = d_outerFacts[d_outerFactHead++];
    Node a = d_egraph.getNode(f.d_a);
    Node b = d_egraph.getNode(f.d_b);
    if (a == b || (f.d_pol && d_egraph.areEqual(f.d_a, f.d_b)))
    {
      continue;
    }
    d_stats.d_numOuterFacts++;
    if (!assignOuter(a.eqNode(b), f.d_pol))
    {
      return false;
    }
  }
  return true;
}

bool InnerSmtSolver::checkTouchedClasses(bool& progress)
{
  // z3 does not need this, since its instances live in the solver that owns
  // the disequalities. We only look at the classes that grew: a disequality
  // between two outer classes can only be violated by a merge of ours that
  // puts them in the same class, and a disequality asserted after that merge
  // is reported by notifyDiseq.
  std::unordered_set<TermId> done;
  while (d_touchedHead < d_touched.size())
  {
    TermId r = d_egraph.find(d_touched[d_touchedHead++]);
    if (d_egraph.isBoolean(r) || !done.insert(r).second)
    {
      continue;
    }
    // one term for each of the outer classes in the class of r
    std::vector<TermId> reps;
    std::unordered_set<ENode*> seen;
    TermId t = r;
    do
    {
      ENode* e = d_mirror.getENode(d_egraph.getNode(t));
      if (e != nullptr && seen.insert(e->getRoot()).second)
      {
        reps.push_back(t);
      }
      t = d_egraph.getNext(t);
    } while (t != r);
    for (size_t i = 0, nreps = reps.size(); i < nreps; i++)
    {
      TNode ni = d_egraph.getNode(reps[i]);
      for (size_t j = i + 1; j < nreps; j++)
      {
        TNode nj = d_egraph.getNode(reps[j]);
        if (!d_qstate.areDisequal(ni, nj))
        {
          continue;
        }
        d_stats.d_numOuterFacts++;
        progress = true;
        if (!assignOuter(ni.eqNode(nj), false))
        {
          return false;
        }
      }
    }
  }
  return true;
}

//------------------------------------------------------------ propagation

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
    switch (kind)
    {
      case ReasonKind::OUTER:
        // l is not assigned, so collectRoots takes it as the outer fact it is
        d_conflictExp.push_back(l);
        break;
      case ReasonKind::CLAUSE:
        // every literal of the clause is false
        for (LitId cl : d_clauses[clause].d_lits)
        {
          if (cl != l)
          {
            d_conflictExp.push_back(litNot(cl));
          }
        }
        d_conflictClause = clause;
        break;
      case ReasonKind::THEORY:
        d_conflictExp.insert(d_conflictExp.end(), exp.begin(), exp.end());
        break;
    }
    return false;
  }
  Atom& a = d_atoms[litAtom(l)];
  a.d_value = litNeg(l) ? Value::FALSE : Value::TRUE;
  a.d_trailIndex = d_assignTrail.size();
  d_assignTrail.push_back(
      Assignment{l, kind, clause, std::move(exp), currentLevel()});
  d_queue.push_back(l);
  d_stats.d_numAssignments++;
  Trace("eager-inner-debug") << "  assign " << getLitNode(l) << std::endl;
  return assertToTheory(l);
}

void InnerSmtSolver::toLits(const std::vector<Node>& exp,
                            std::vector<LitId>& lits) const
{
  for (const Node& e : exp)
  {
    std::map<Node, size_t>::const_iterator it =
        d_atomMap.find(e.getKind() == Kind::NOT ? e[0] : e);
    Assert(it != d_atomMap.end());
    lits.push_back(mkLit(it->second, e.getKind() == Kind::NOT));
  }
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
  toLits(d_egraph.getConflict(), d_conflictExp);
  return false;
}

bool InnerSmtSolver::visitClause(size_t c)
{
  const Clause& cl = d_clauses[c];
  if (!cl.d_active)
  {
    return true;
  }
  LitId unassigned = undefinedLit;
  size_t numUnassigned = 0;
  for (LitId cli : cl.d_lits)
  {
    Value v = value(cli);
    if (v == Value::TRUE)
    {
      return true;
    }
    if (v == Value::UNDEF)
    {
      unassigned = cli;
      if (++numUnassigned > 1)
      {
        return true;
      }
    }
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
  return assign(unassigned, ReasonKind::CLAUSE, c, {});
}

bool InnerSmtSolver::propagate()
{
  for (;;)
  {
    // the clauses added since the last round
    while (d_clauseHead < d_clauses.size())
    {
      if (!visitClause(d_clauseHead++))
      {
        return false;
      }
    }
    while (!d_queue.empty())
    {
      LitId l = d_queue.back();
      d_queue.pop_back();
      // the clauses in which l is false
      size_t atom = litAtom(litNot(l));
      for (size_t i = 0; i < d_atoms[atom].d_occurs.size(); i++)
      {
        if (!visitClause(d_atoms[atom].d_occurs[i]))
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
    if (!progress && !checkTouchedClasses(progress))
    {
      return false;
    }
    if (!progress && d_queue.empty())
    {
      return true;
    }
  }
}

bool InnerSmtSolver::theoryPropagate(bool& progress)
{
  // The candidates are the atoms watching a term whose class was merged,
  // collected by notifyMerge. z3 finds them through the congruence table.
  while (d_candidateHead < d_candidates.size())
  {
    size_t i = d_candidates[d_candidateHead++];
    if (i >= d_atoms.size() || d_atoms[i].d_value != Value::UNDEF)
    {
      continue;
    }
    const Atom& a = d_atoms[i];
    bool implied = false;
    bool pol = true;
    if (a.d_lhs != InnerEGraph::undefinedTerm)
    {
      implied = d_egraph.areEqual(a.d_lhs, a.d_rhs);
    }
    else if (a.d_term != InnerEGraph::undefinedTerm)
    {
      if (d_egraph.areEqual(a.d_term, d_trueTerm))
      {
        implied = true;
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
    toLits(exp, expLits);
    progress = true;
    if (!assign(mkLit(i, !pol), ReasonKind::THEORY, 0, std::move(expLits)))
    {
      return false;
    }
  }
  return true;
}

//------------------------------------------------------------ explanations

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
    const Atom& at = d_atoms[litAtom(curr)];
    if (at.d_trailIndex == noIndex
        || d_assignTrail[at.d_trailIndex].d_lit != curr)
    {
      // not assigned by us, so it is an outer fact
      outerLits.insert(getLitNode(curr));
      continue;
    }
    const Assignment& asgn = d_assignTrail[at.d_trailIndex];
    switch (asgn.d_kind)
    {
      case ReasonKind::OUTER: outerLits.insert(getLitNode(curr)); break;
      case ReasonKind::CLAUSE:
      {
        const Clause& cl = d_clauses[asgn.d_clause];
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
        todo.insert(todo.end(), asgn.d_exp.begin(), asgn.d_exp.end());
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
    d_usedInstanceIdx.push_back(i);
  }
}

void InnerSmtSolver::deactivateUsedInstances()
{
  for (size_t i : d_usedInstanceIdx)
  {
    Assert(i < d_instances.size());
    size_t begin = d_instances[i].d_clauseBegin;
    size_t end = i + 1 < d_instances.size() ? d_instances[i + 1].d_clauseBegin
                                            : d_clauses.size();
    bool any = false;
    for (size_t c = begin; c < end && c < d_clauses.size(); c++)
    {
      if (!d_clauses[c].d_active)
      {
        continue;
      }
      d_clauses[c].d_active = false;
      // the index, not a pointer: d_clauses can reallocate. On a pop the
      // clauses may already have been dropped, hence the bound check.
      d_trail.onPop([this, c]() {
        if (c < d_clauses.size())
        {
          d_clauses[c].d_active = true;
        }
      });
      any = true;
    }
    if (any)
    {
      d_stats.d_numDeactivated++;
      Trace("eager-inner") << "InnerSmtSolver: hand off instance "
                           << d_instances[i].d_lemma << std::endl;
    }
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

void InnerSmtSolver::exportPropagations()
{
  // Export a bounded number of the literals derived since the last round that
  // the outer solver has a variable for but no value.
  Valuation& val = d_qstate.getValuation();
  while (d_exportHead < d_assignTrail.size()
         && d_propagations.size() < s_maxPropagationsPerRound)
  {
    const Assignment& a = d_assignTrail[d_exportHead++];
    if (a.d_kind == ReasonKind::OUTER)
    {
      continue;
    }
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
    d_propagations.emplace_back(getLitNode(a.d_lit), exp);
    noteUsedInstances(instances);
    d_stats.d_numPropagations++;
  }
}

size_t InnerSmtSolver::levelOf(LitId l) const
{
  size_t idx = d_atoms[litAtom(l)].d_trailIndex;
  if (idx >= d_assignTrail.size() || d_assignTrail[idx].d_lit != l)
  {
    return 0;
  }
  return d_assignTrail[idx].d_level;
}

InnerSmtSolver::LitId InnerSmtSolver::pickDecision()
{
  // A clause with no true literal needs one of its literals to become true.
  // Propagation has already run, so such a clause has at least two unassigned
  // literals and choosing either of them is a real choice.
  size_t nc = d_clauses.size();
  for (size_t k = 0; k < nc; k++)
  {
    size_t c = (d_decisionHint + k) % nc;
    if (!d_clauses[c].d_active)
    {
      continue;
    }
    LitId cand = undefinedLit;
    bool satisfied = false;
    for (LitId l : d_clauses[c].d_lits)
    {
      Value v = value(l);
      if (v == Value::TRUE)
      {
        satisfied = true;
        break;
      }
      if (v == Value::UNDEF && cand == undefinedLit)
      {
        cand = l;
      }
    }
    if (!satisfied && cand != undefinedLit)
    {
      d_decisionHint = c;
      return cand;
    }
  }
  return undefinedLit;
}

void InnerSmtSolver::conflictAntecedents(const std::vector<LitId>& exp,
                                         std::vector<LitId>& ants) const
{
  std::unordered_set<LitId> seen;
  std::vector<LitId> todo;
  for (LitId l : exp)
  {
    if (l != undefinedLit)
    {
      todo.push_back(l);
    }
  }
  while (!todo.empty())
  {
    LitId curr = todo.back();
    todo.pop_back();
    if (!seen.insert(curr).second)
    {
      continue;
    }
    size_t idx = d_atoms[litAtom(curr)].d_trailIndex;
    if (idx >= d_assignTrail.size() || d_assignTrail[idx].d_lit != curr)
    {
      // not assigned by us, so it is as good as an outer fact
      ants.push_back(curr);
      continue;
    }
    const Assignment& a = d_assignTrail[idx];
    switch (a.d_kind)
    {
      case ReasonKind::OUTER:
      case ReasonKind::DECISION: ants.push_back(curr); break;
      case ReasonKind::CLAUSE:
        for (LitId cli : d_clauses[a.d_clause].d_lits)
        {
          if (cli != curr)
          {
            todo.push_back(litNot(cli));
          }
        }
        break;
      case ReasonKind::THEORY:
        for (LitId e : a.d_exp)
        {
          todo.push_back(e);
        }
        break;
    }
  }
}

bool InnerSmtSolver::search()
{
  uint64_t conflicts = 0;
  Checkpoint preSearch = mkCheckpoint();
  for (;;)
  {
    if (propagate())
    {
      LitId d = d_budget == 0 ? undefinedLit : pickDecision();
      if (d == undefinedLit)
      {
        // Every clause is satisfied, so the instances are consistent with the
        // outer facts and there is nothing to report.
        if (d_decisions.empty())
        {
          d_stats.d_numSaturated++;
        }
        else
        {
          // what the decisions implied is not entailed, so it is undone
          restoreTo(preSearch);
          d_decisions.clear();
        }
        return true;
      }
      d_decisions.push_back(Decision{d, mkCheckpoint()});
      d_stats.d_numDecisions++;
      Trace("eager-inner-debug") << "  decide " << getLitNode(d) << " at level "
                                 << currentLevel() << std::endl;
      // a decision cannot conflict, it is chosen unassigned
      assign(d, ReasonKind::DECISION, 0, {});
      continue;
    }
    // A conflict. It only refutes the decisions it used, so it is exportable
    // only if it used none, i.e. if it follows from the outer facts and the
    // instances alone.
    std::vector<LitId> ants;
    conflictAntecedents(d_conflictExp, ants);
    size_t maxLevel = 0;
    for (LitId a : ants)
    {
      maxLevel = std::max(maxLevel, levelOf(a));
    }
    if (maxLevel == 0)
    {
      return false;
    }
    conflicts++;
    d_stats.d_numSearchConflicts++;
    if (conflicts > d_budget)
    {
      d_stats.d_numBudgetOut++;
      restoreTo(preSearch);
      d_decisions.clear();
      d_conflictExp.clear();
      return true;
    }
    // Undo the decision at the deepest level the conflict used and assert its
    // negation, which the remaining antecedents imply.
    Assert(maxLevel <= d_decisions.size());
    LitId dec = d_decisions[maxLevel - 1].d_lit;
    Checkpoint cp = d_decisions[maxLevel - 1].d_cp;
    std::vector<LitId> exp;
    for (LitId a : ants)
    {
      if (a != dec)
      {
        exp.push_back(a);
      }
    }
    restoreTo(cp);
    d_decisions.resize(maxLevel - 1);
    d_conflictExp.clear();
    Trace("eager-inner-debug") << "  backjump to level " << currentLevel()
                               << ", flip " << getLitNode(dec) << std::endl;
    if (!assign(litNot(dec), ReasonKind::THEORY, 0, exp))
    {
      // the flip conflicts at this level, which the next iteration resolves
      continue;
    }
  }
}

bool InnerSmtSolver::check()
{
  d_stats.d_numChecks++;
  d_conflict = Node::null();
  d_usedInstantiations.clear();
  d_usedInstanceIdx.clear();
  d_conflictClause = d_clauses.size();
  if (d_clauses.empty())
  {
    return true;
  }
  ensureScopeSaved();
  // A round that ends in a conflict is undone, so that the state stays
  // consistent; the outer solver backtracks once it sees the conflict.
  Checkpoint start = mkCheckpoint();
  bool ok = true;
  // The terms of the instances added since the last round may have merged two
  // classes that are disequal, which the congruence closure does not report
  // at the time.
  if (!d_egraph.checkDisequalities())
  {
    toLits(d_egraph.getConflict(), d_conflictExp);
    ok = false;
  }
  ok = ok && syncOuter() && processOuterFacts() && search();
  if (!ok)
  {
    Node conf = mkConflict(d_conflictExp);
    restoreTo(start);
    if (conf.isNull())
    {
      return true;
    }
    d_conflict = conf;
    d_stats.d_numConflicts++;
    Trace("eager-inner") << "InnerSmtSolver: conflict " << d_conflict
                         << std::endl;
    return false;
  }
  if (d_propagateOut)
  {
    exportPropagations();
  }
  return true;
}

void InnerSmtSolver::debugPrint(std::ostream& out) const
{
  out << "inner-smt-solver: " << d_instances.size() << " instances, "
      << d_clauses.size() << " clauses, " << d_atoms.size() << " atoms, "
      << d_assignTrail.size() << " assigned" << std::endl;
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
