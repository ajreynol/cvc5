/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bridges from cvc5's own theory solvers into the ported Z3 core.
 */

#include "z3/theory_cvc5.h"

#include <algorithm>
#include <chrono>
#include <sstream>
#include <unordered_set>

#include "base/output.h"
#include "options/base_options.h"
#include "options/option_exception.h"
#include "options/arith_options.h"
#include "options/smt_options.h"
#include "options/z3_options.h"
#include "smt/env.h"
#include "smt/set_defaults.h"
#include "smt/solver_engine.h"
#include "expr/skolem_manager.h"
#include "theory/smt_engine_subsolver.h"
#include "util/rational.h"
#include "util/result.h"
#include "z3/ast.h"
#include "z3/justification.h"
#include "z3/smt_context.h"

namespace cvc5::internal {
namespace z3 {

namespace {

/** Accumulates the wall time of one subsolver check. */
class BridgeTimer
{
 public:
  BridgeTimer(uint64_t& total,
              std::chrono::steady_clock::time_point start)
      : d_total(total), d_start(start)
  {
  }

  ~BridgeTimer()
  {
    d_total += static_cast<uint64_t>(
        std::chrono::duration_cast<std::chrono::milliseconds>(
            std::chrono::steady_clock::now() - d_start)
            .count());
  }

 private:
  uint64_t& d_total;
  std::chrono::steady_clock::time_point d_start;
};

}  // namespace

// ----------------------------------------------------------------- bridge

Cvc5Bridge::Cvc5Bridge(SmtContext& ctx)
    : d_ctx(ctx), d_subFailed(false), d_assertedBaseLvl(0)
{
}

Cvc5Bridge::~Cvc5Bridge() {}

void Cvc5Bridge::addTheory(TheoryCvc5* th) { d_theories.push_back(th); }

bool Cvc5Bridge::isOwner(const TheoryCvc5* th) const
{
  return !d_theories.empty() && d_theories.front() == th;
}

void Cvc5Bridge::registerAtom(TNode atom, BoolVar v)
{
  d_ctx.pushTrail(
      PushBackVector<std::vector<std::pair<Node, BoolVar>>>(d_atoms));
  d_atoms.push_back(std::pair<Node, BoolVar>(atom, v));
}

void Cvc5Bridge::registerTerm(TNode term)
{
  d_ctx.pushTrail(PushBackVector<std::vector<Node>>(d_terms));
  d_terms.push_back(term);
}

void Cvc5Bridge::reset()
{
  d_sub.reset(nullptr);
  d_subFailed = false;
  d_atoms.clear();
  d_terms.clear();
  d_antecedents.clear();
  d_asserted.clear();
  d_abs.clear();
  d_actOf.clear();
  d_litOf.clear();
  d_monomials.clear();
  d_linLemmas.clear();
  d_haveModel = false;
  d_satSets.clear();
  d_satSetsTermsLim = 0;
  d_unsatCores.clear();
  d_known.clear();
}

bool Cvc5Bridge::initSubsolver()
{
  if (d_sub != nullptr)
  {
    return true;
  }
  if (d_subFailed)
  {
    return false;
  }
  try
  {
    const Env& env = d_ctx.getEnv();
    Options subOptions;
    subOptions.copyValues(env.getOptions());
    // The subsolver must be cvc5's own solver, not another ported core.
    subOptions.write_z3().z3 = false;
    subOptions.write_smt().unsatAssumptions = true;
    subOptions.write_smt().produceModels = true;
    subOptions.write_base().incrementalSolving = true;
    // The subsolver is called hundreds of times on a slowly growing set of
    // literals, so the passes that pay off once on a whole query are a net
    // loss here.
    subOptions.write_smt().simplificationMode =
        options::SimplificationMode::NONE;
    subOptions.write_smt().staticLearning = false;
    // Z3's arithmetic solver only ever makes a bounded effort: the nonlinear
    // rounds of theory_arith are capped and it answers FC_GIVEUP rather than
    // searching on, which is why its 85 final checks on an NIA query each
    // cost almost nothing. The subsolver has to behave the same way, because
    // the ported core only makes progress *between* the calls -- one
    // unbounded nonlinear search starves the instantiation loop that actually
    // closes these queries, and model-based refinement on a satisfiable
    // nonlinear subproblem does not terminate. Giving up is safe: it taints
    // the model, so a final "sat" becomes "unknown", but the core may still
    // derive unsat from the instances it goes on to produce.
    if (env.getOptions().z3.z3BridgeRlimitPer != 0)
    {
      subOptions.write_base().perCallResourceLimit =
          env.getOptions().z3.z3BridgeRlimitPer;
    }
    if (!d_ctx.getParams().d_arithNl)
    {
      // smt.arith.nl=false: theory_arith treats each monomial as an opaque
      // variable of the simplex and, at final check, answers FC_DONE if the
      // assignment happens to satisfy every monomial and FC_GIVEUP otherwise
      // (process_non_linear). cvc5's nonlinear extension with no
      // linearization and no cylindrical algebraic coverings does the same:
      // the linear abstraction, then a check of the model, then "unknown".
      subOptions.write_arith().nlExt = options::NlExtMode::NONE;
      subOptions.write_arith().nlExtWasSetByUser = true;
      subOptions.write_arith().nlCov = false;
      subOptions.write_arith().nlCovWasSetByUser = true;
    }
    smt::SetDefaults::disableChecking(subOptions);
    theory::SubsolverSetupInfo ssi(env, subOptions);
    theory::initializeSubsolver(env.getNodeManager(), d_sub, ssi);
  }
  catch (const std::exception& e)
  {
    Trace("z3") << "cvc5 bridge: could not create the subsolver: " << e.what()
                << std::endl;
    d_sub.reset(nullptr);
    d_subFailed = true;
    return false;
  }
  return true;
}

bool Cvc5Bridge::mkAssumptions(std::vector<Node>& assumps)
{
  d_antecedents.clear();
  // 1. the assigned atoms of the bridged theories
  for (const std::pair<Node, BoolVar>& ab : d_atoms)
  {
    BoolVar v = ab.second;
    if (v >= static_cast<BoolVar>(d_ctx.getNumBoolVars()))
    {
      // the variable was deleted by backtracking
      continue;
    }
    LBool val = d_ctx.getAssignment(v);
    if (val == L_UNDEF)
    {
      continue;
    }
    if (!d_ctx.isRelevant(v))
    {
      // Z3's theory solvers only ever see the relevant atoms: an assignment
      // is forwarded to a theory from the atom propagation queue, which an
      // atom only enters once it is relevant. Dropping the irrelevant ones
      // keeps the subsolver's job the size Z3's arithmetic solver would see.
      continue;
    }
    Node absAtom = abstract(ab.first);
    Node lit = val == L_TRUE ? absAtom : absAtom.notNode();
    if (d_ctx.getAssignLevel(v) <= d_ctx.getBaseLevel())
    {
      // A literal the core assigned at its base level never retracts, so it
      // can be asserted to the subsolver once instead of being re-sent and
      // re-preprocessed on every call. It is also not needed as an
      // antecedent of a conflict: conflict resolution drops the literals
      // assigned at or below the base level anyway.
      if (d_asserted.insert(lit).second)
      {
        d_ctx.getStats().d_bridgeAsserted++;
        std::vector<Node> one{lit};
        collectKnown(one);
        try
        {
          d_sub->assertFormula(lit);
        }
        catch (const std::exception&)
        {
          d_asserted.erase(lit);
          assumps.push_back(lit);
          Antecedent a;
          a.d_lit = Literal(v, val == L_FALSE);
          d_antecedents[lit] = a;
        }
      }
      continue;
    }
    if (d_antecedents.count(lit) != 0)
    {
      continue;
    }
    Antecedent a;
    a.d_lit = Literal(v, val == L_FALSE);
    d_antecedents[lit] = a;
    assumps.push_back(lit);
  }
  // 2. the equalities the core derived between terms of a bridged sort,
  //    which is the half of the Nelson-Oppen interface the subsolver needs
  std::unordered_map<ENode*, ENode*> rep;
  for (const Node& t : d_terms)
  {
    if (!d_ctx.eInternalized(t))
    {
      continue;
    }
    ENode* e = d_ctx.getENode(t);
    ENode* r = e->getRoot();
    auto it = rep.find(r);
    if (it == rep.end())
    {
      rep[r] = e;
      continue;
    }
    if (it->second == e)
    {
      continue;
    }
    Node eq = abstract(it->second->getExpr()).eqNode(abstract(e->getExpr()));
    if (eq[0] == eq[1] || d_antecedents.count(eq) != 0)
    {
      continue;
    }
    Antecedent a;
    a.d_eq = ENodePair(it->second, e);
    d_antecedents[eq] = a;
    assumps.push_back(eq);
  }
  collectKnown(assumps);
  if (!d_ctx.getParams().d_arithNl)
  {
    linearizeMonomials();
  }
  return true;
}

void Cvc5Bridge::collectKnown(const std::vector<Node>& assumps)
{
  // Only the terms that occur in something the subsolver was given are known
  // to it; asking for the value of any other one is pointless and noisy.
  // Note d_known is not cleared: the permanent assertions stay known.
  std::vector<TNode> visit;
  for (const Node& a : assumps)
  {
    visit.push_back(a);
  }
  while (!visit.empty())
  {
    TNode cur = visit.back();
    visit.pop_back();
    if (!d_known.insert(cur).second)
    {
      continue;
    }
    for (const Node& c : cur)
    {
      visit.push_back(c);
    }
  }
}

FinalCheckStatus Cvc5Bridge::check(bool finalCheck)
{
  auto start = std::chrono::steady_clock::now();
  BridgeTimer timer(d_ctx.getStats().d_bridgeTimeMs, start);
  if (d_atoms.empty() && d_terms.empty())
  {
    return FC_DONE;
  }
  if (!initSubsolver())
  {
    d_ctx.markModelUnsound(theory::THEORY_ARITH);
    return FC_DONE;
  }
  if (d_ctx.getBaseLevel() != d_assertedBaseLvl && !d_asserted.empty())
  {
    // The base level moved, so the permanent assertions are no longer known
    // to hold: start the subsolver over.
    reset();
    if (!initSubsolver())
    {
      d_ctx.markModelUnsound(theory::THEORY_ARITH);
      return FC_DONE;
    }
  }
  d_assertedBaseLvl = d_ctx.getBaseLevel();
  std::vector<Node> assumps;
  mkAssumptions(assumps);
  // Backtracking brings the search back to a set of literals the subsolver
  // has already judged, and the subsolver is by far the most expensive part
  // of a final check, so both verdicts are remembered. Note neither depends
  // on the scope: a set of literals is satisfiable or not on its own.
  if (d_terms.size() != d_satSetsTermsLim)
  {
    // New bridged terms may have made a class shared that was not before, so
    // the interface reconciliation of the remembered sets no longer applies.
    d_satSets.clear();
    d_satSetsTermsLim = d_terms.size();
  }
  std::vector<Node> key = assumps;
  std::sort(key.begin(), key.end());
  if (d_satSets.count(key) != 0)
  {
    return FC_DONE;
  }
  std::unordered_set<Node> cur(assumps.begin(), assumps.end());
  for (const std::vector<Node>& core : d_unsatCores)
  {
    bool present = true;
    for (const Node& c : core)
    {
      if (cur.count(c) == 0)
      {
        present = false;
        break;
      }
    }
    if (present)
    {
      Trace("z3-bridge") << "cvc5 bridge: replaying a known conflict"
                         << std::endl;
      d_ctx.getStats().d_numBridgeConflicts++;
      mkConflict(core);
      return FC_CONTINUE;
    }
  }
  d_lastCheckAssignments = d_ctx.getStats().d_numAssignments;
  d_ctx.getStats().d_bridgeAssumptions += assumps.size();
  Trace("z3-bridge") << "cvc5 bridge: check " << assumps.size()
                     << " assumptions, " << d_atoms.size() << " atoms, "
                     << d_terms.size() << " terms" << std::endl;
  if (TraceIsOn("z3-bridge-detail"))
  {
    for (const Node& a : assumps)
    {
      Trace("z3-bridge-detail") << "  assume " << a << std::endl;
    }
  }
  Result r;
  try
  {
    r = checkSub(assumps);
  }
  catch (const std::exception& e)
  {
    Trace("z3") << "cvc5 bridge: the subsolver failed: " << e.what()
                << std::endl;
    d_haveModel = false;
    d_ctx.markModelUnsound(theory::THEORY_ARITH);
    return FC_DONE;
  }
  d_ctx.getStats().d_numBridgeChecks++;
  d_haveModel = r.getStatus() == Result::SAT;
  if (d_haveModel)
  {
    // The two solvers agree on the literals. Their models still have to agree
    // on the terms they share, which is what the interface equalities below
    // establish.
    FinalCheckStatus st = FC_DONE;
    if (finalCheck)
    {
      // The order is Z3's. First the model is asked to keep the shared terms
      // apart wherever it can, which is what random_update does there. Then
      // the equalities that survive that are *entailed*, so they are
      // propagated rather than split on -- Z3's arithmetic solver propagates
      // thousands of these (arith-fixed-eqs) and splits on a few dozen
      // (arith-assume-eqs). Splitting first instead hands the core tens of
      // thousands of equalities that were entailed all along, and never
      // creates the numeral enodes the propagation does.
      //
      // The propagation half is off by default. Z3 gets it for free -- its
      // simplex notices that a variable's bounds have met -- while here every
      // one of those equalities costs a subsolver query to establish, and on
      // the benchmark this was measured on that bought nineteen merges for
      // five seconds. What it would buy is real (the merge creates the
      // numeral's enode, and patterns like (Add 8 0) only match once it
      // exists), so the code stays, behind --z3-bridge-fixed-eqs, until the
      // bridge can answer the question without a query per group.
      separateSharedValues(assumps);
      if (d_ctx.getEnv().getOptions().z3.z3BridgeFixedEqs
          && propagateFixedEqs(assumps))
      {
        st = FC_CONTINUE;
      }
      else
      {
        restoreModel(assumps);
        st = assumeInterfaceEqs();
      }
    }
    // process_non_linear comes last in theory_arith's final check, after
    // assume_eqs: with smt.arith.nl=false it answers FC_DONE if the
    // assignment happens to satisfy every monomial and FC_GIVEUP otherwise.
    bool monomialsOk = true;
    if (st == FC_DONE && !d_monomials.empty() && !checkMonomials())
    {
      monomialsOk = false;
      d_ctx.markModelUnsound(theory::THEORY_ARITH);
    }
    if (st == FC_DONE)
    {
      if (monomialsOk && d_satSets.size() < s_maxCachedSatSets)
      {
        d_satSets.insert(key);
      }
      // Nothing came of this call, so wait longer before the next one.
      d_eagerGap = std::min(s_maxEagerGap, d_eagerGap * 2);
    }
    else
    {
      d_eagerGap = std::max(s_minEagerGap, d_eagerGap / 2);
    }
    return st;
  }
  if (r.getStatus() != Result::UNSAT)
  {
    d_ctx.markModelUnsound(theory::THEORY_ARITH);
    return FC_DONE;
  }
  d_ctx.getStats().d_numBridgeConflicts++;
  d_eagerGap = std::max(s_minEagerGap, d_eagerGap / 2);
  std::vector<Node> core = unsatCore();
  if (d_unsatCores.size() < s_maxCachedCores)
  {
    d_unsatCores.push_back(core);
  }
  mkConflict(core);
  return FC_CONTINUE;
}

void Cvc5Bridge::mkConflict(const std::vector<Node>& core)
{
  LiteralVector lits;
  ENodePairVector eqs;
  for (const Node& a : core)
  {
    auto it = d_antecedents.find(a);
    if (it == d_antecedents.end())
    {
      // The subsolver should only return assumptions it was given.
      Assert(false);
      continue;
    }
    if (it->second.d_eq.first != nullptr)
    {
      eqs.push_back(it->second.d_eq);
    }
    else
    {
      lits.push_back(it->second.d_lit);
    }
  }
  Trace("z3-bridge") << "cvc5 bridge: conflict with " << lits.size()
                     << " literals and " << eqs.size() << " equalities"
                     << std::endl;
  d_ctx.setConflict(d_ctx.mkJustification(
      ExtTheoryConflictJustification(theory::THEORY_ARITH,
                                     d_ctx,
                                     lits.size(),
                                     lits.data(),
                                     eqs.size(),
                                     eqs.data())));
}

bool Cvc5Bridge::isBridgedType(const TypeNode& tn)
{
  return tn.isRealOrInt() || tn.isBitVector();
}

bool Cvc5Bridge::isBridgedOp(Kind k)
{
  if (k == Kind::NOT || k == Kind::EQUAL)
  {
    return true;
  }
  TheoryId tid = theory::kindToTheoryId(k);
  return tid == theory::THEORY_ARITH || tid == theory::THEORY_BV;
}

Node Cvc5Bridge::abstract(TNode t)
{
  auto it = d_abs.find(t);
  if (it != d_abs.end())
  {
    return it->second;
  }
  Node ret;
  if (t.getNumChildren() == 0)
  {
    // A leaf of a bridged sort is an arithmetic or bit-vector variable or
    // constant and is kept; anything else cannot occur in a bridged atom
    // except as an opaque value.
    ret = isBridgedType(t.getType()) ? Node(t) : mkAbsConst(t);
  }
  else if (!d_ctx.getParams().d_arithNl && isNonlinear(t))
  {
    // smt.arith.nl=false: the simplex sees a monomial as a variable of its
    // own, so the subsolver gets an opaque constant. Its arguments are still
    // abstracted, since linearizeMonomials and checkMonomials refer to them.
    for (const Node& c : t)
    {
      abstract(c);
    }
    ret = mkAbsConst(t);
    d_monomials.emplace_back(t, ret);
  }
  else if (isBridgedOp(t.getKind()))
  {
    std::vector<Node> children;
    if (t.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      children.push_back(t.getOperator());
    }
    for (const Node& c : t)
    {
      children.push_back(abstract(c));
    }
    ret = d_ctx.getEnv().getNodeManager()->mkNode(t.getKind(), children);
  }
  else
  {
    ret = mkAbsConst(t);
  }
  d_abs[t] = ret;
  return ret;
}

bool Cvc5Bridge::isNonlinear(TNode t)
{
  switch (t.getKind())
  {
    case Kind::NONLINEAR_MULT: return true;
    case Kind::DIVISION:
    case Kind::DIVISION_TOTAL:
    case Kind::INTS_DIVISION:
    case Kind::INTS_DIVISION_TOTAL:
    case Kind::INTS_MODULUS:
    case Kind::INTS_MODULUS_TOTAL: return !t[1].isConst();
    default: return false;
  }
}

Node Cvc5Bridge::getFixedValue(TNode t)
{
  if (t.isConst())
  {
    return t;
  }
  if (!d_ctx.eInternalized(t))
  {
    return Node::null();
  }
  ENode* e = d_ctx.getENode(t);
  ENode* n = e;
  do
  {
    if (n->getExpr().isConst())
    {
      return n->getExpr();
    }
    n = n->getNext();
  } while (n != e);
  return Node::null();
}

void Cvc5Bridge::linearizeMonomials()
{
  NodeManager* nm = d_ctx.getEnv().getNodeManager();
  for (const std::pair<Node, Node>& m : d_monomials)
  {
    if (d_known.count(m.second) == 0)
    {
      continue;
    }
    TNode t = m.first;
    std::vector<Node> premises;
    Node conclusion;
    if (t.getKind() == Kind::NONLINEAR_MULT)
    {
      Rational k(1);
      std::vector<Node> free;
      for (const Node& c : t)
      {
        Node v = getFixedValue(c);
        if (v.isNull())
        {
          free.push_back(c);
          continue;
        }
        Node prem = abstract(c).eqNode(v);
        if (v.getConst<Rational>().isZero())
        {
          // One of the factors is zero, which fixes the product.
          premises = {prem};
          k = Rational(0);
          free.clear();
          break;
        }
        premises.push_back(prem);
        k *= v.getConst<Rational>();
      }
      if (free.size() > 1)
      {
        continue;
      }
      Node kn = nm->mkConstRealOrInt(t.getType(), k);
      conclusion = free.empty()
                       ? m.second.eqNode(kn)
                       : m.second.eqNode(
                           nm->mkNode(Kind::MULT, kn, abstract(free[0])));
    }
    else
    {
      // A division by a fixed divisor is linear.
      Node v = getFixedValue(t[1]);
      if (v.isNull() || v.getConst<Rational>().isZero())
      {
        continue;
      }
      premises.push_back(abstract(t[1]).eqNode(v));
      conclusion =
          m.second.eqNode(nm->mkNode(t.getKind(), abstract(t[0]), v));
    }
    Node lem = premises.empty()
                   ? conclusion
                   : nm->mkNode(Kind::IMPLIES,
                                premises.size() == 1
                                    ? premises[0]
                                    : nm->mkNode(Kind::AND, premises),
                                conclusion);
    if (d_linLemmas.insert(lem).second)
    {
      // Valid by the definition of the abstraction, so it is asserted once
      // and for all rather than assumed.
      d_sub->assertFormula(lem);
    }
  }
}

bool Cvc5Bridge::checkMonomials()
{
  NodeManager* nm = d_ctx.getEnv().getNodeManager();
  for (const std::pair<Node, Node>& m : d_monomials)
  {
    if (d_known.count(m.second) == 0)
    {
      continue;
    }
    std::vector<Node> children;
    for (const Node& c : m.first)
    {
      children.push_back(abstract(c));
    }
    Node def = nm->mkNode(m.first.getKind(), children);
    try
    {
      if (d_sub->getValue(m.second) != d_sub->getValue(def))
      {
        return false;
      }
    }
    catch (const std::exception&)
    {
      return false;
    }
  }
  return true;
}

Result Cvc5Bridge::checkSub(const std::vector<Node>& assumps)
{
  if (!d_ctx.getEnv().getOptions().z3.z3BridgeActivation)
  {
    return d_sub->checkSat(assumps);
  }
  std::vector<Node> acts;
  acts.reserve(assumps.size());
  for (const Node& a : assumps)
  {
    acts.push_back(d_antecedents.count(a) != 0 ? activation(a) : a);
  }
  return d_sub->checkSat(acts);
}

std::vector<Node> Cvc5Bridge::unsatCore()
{
  std::vector<Node> core;
  for (const Node& a : d_sub->getUnsatAssumptions())
  {
    auto it = d_litOf.find(a);
    core.push_back(it == d_litOf.end() ? a : it->second);
  }
  return core;
}

Node Cvc5Bridge::activation(const Node& lit)
{
  auto it = d_actOf.find(lit);
  if (it != d_actOf.end())
  {
    return it->second;
  }
  NodeManager* nm = d_ctx.getEnv().getNodeManager();
  Node act = nm->getSkolemManager()->mkDummySkolem("z3act", nm->booleanType());
  d_sub->assertFormula(nm->mkNode(Kind::IMPLIES, act, lit));
  d_actOf[lit] = act;
  d_litOf[act] = lit;
  return act;
}

Node Cvc5Bridge::mkAbsConst(TNode t)
{
  SkolemManager* sm = d_ctx.getEnv().getNodeManager()->getSkolemManager();
  return sm->mkDummySkolem("z3abs", t.getType());
}

bool Cvc5Bridge::isBridged(TheoryId tid)
{
  return tid == theory::THEORY_ARITH || tid == theory::THEORY_BV;
}

bool Cvc5Bridge::shouldCheckEagerly() const
{
  return d_ctx.getStats().d_numAssignments >= d_lastCheckAssignments + d_eagerGap;
}

Node Cvc5Bridge::getModelValue(TNode t)
{
  if (!d_haveModel)
  {
    return Node::null();
  }
  Node at = abstract(t);
  if (d_known.count(at) == 0)
  {
    // The subsolver has never seen this term, so it does not constrain its
    // value and the core is free to choose one.
    return Node::null();
  }
  Node val;
  try
  {
    // getValue warns when the model cannot evaluate the term, which here is
    // an expected outcome rather than a problem worth reporting. Note the
    // previous stream has to be read before the swap: setStream returns the
    // stream it was *given*, not the one it replaced, so taking its address
    // would leave the channel pointing at this local buffer afterwards.
    std::stringstream dropped;
    std::ostream* prev = WarningChannel.getStreamPointer();
    WarningChannel.setStream(&dropped);
    try
    {
      val = d_sub->getValue(at);
    }
    catch (...)
    {
      WarningChannel.setStream(prev);
      throw;
    }
    WarningChannel.setStream(prev);
  }
  catch (const std::exception&)
  {
    return Node::null();
  }
  return val;
}

void Cvc5Bridge::collectSharedRoots(std::vector<std::pair<ENode*, Node>>& out)
{
  std::unordered_set<ENode*> seen;
  for (TheoryCvc5* th : d_theories)
  {
    size_t num = th->getNumVars();
    for (size_t v = 0; v < num; ++v)
    {
      ENode* n = th->getENode(static_cast<TheoryVar>(v));
      if (n == nullptr || !d_ctx.isRelevant(n) || !d_ctx.isShared(n))
      {
        continue;
      }
      if (!seen.insert(n->getRoot()).second)
      {
        continue;
      }
      Node val = getModelValue(n->getExpr());
      if (!val.isNull())
      {
        out.push_back(std::pair<ENode*, Node>(n, val));
      }
    }
  }
}

bool Cvc5Bridge::trySeparate(std::vector<Node>& assumps,
                             size_t base,
                             const std::vector<Node>& wanted)
{
  NodeManager* nm = d_ctx.getEnv().getNodeManager();
  assumps.resize(base);
  assumps.push_back(wanted.size() == 1 ? wanted[0]
                                       : nm->mkNode(Kind::AND, wanted));
  Result r;
  try
  {
    r = checkSub(assumps);
  }
  catch (const std::exception&)
  {
    r = Result();
  }
  d_ctx.getStats().d_numBridgeChecks++;
  assumps.resize(base);
  d_haveModel = r.getStatus() == Result::SAT;
  return d_haveModel;
}

bool Cvc5Bridge::separateSharedValues(std::vector<Node>& assumps)
{
  if (!d_haveModel)
  {
    return false;
  }
  std::vector<std::pair<ENode*, Node>> shared;
  collectSharedRoots(shared);
  // Group the shared terms whose values coincide. Only those groups matter:
  // terms the model already keeps apart need nothing.
  std::map<Node, std::vector<Node>> byValue;
  for (const std::pair<ENode*, Node>& p : shared)
  {
    // Two congruence roots can abstract to the same term, in which case
    // asking for them to differ is unsatisfiable for a reason that has
    // nothing to do with arithmetic. The abstraction is what the subsolver
    // reasons about, so it is what has to be distinct.
    std::vector<Node>& g = byValue[p.second];
    Node a = abstract(p.first->getExpr());
    if (std::find(g.begin(), g.end(), a) == g.end())
    {
      g.push_back(a);
    }
  }
  NodeManager* nm = d_ctx.getEnv().getNodeManager();
  std::vector<Node> wanted;
  size_t numCoinciding = 0;
  for (const std::pair<const Node, std::vector<Node>>& g : byValue)
  {
    if (g.second.size() < 2)
    {
      continue;
    }
    numCoinciding += g.second.size();
    wanted.push_back(nm->mkNode(Kind::DISTINCT, g.second));
  }
  if (wanted.empty())
  {
    return true;
  }
  d_ctx.getStats().d_numSharedGroups += wanted.size();
  d_ctx.getStats().d_numCoincidingShared += numCoinciding;
  // All the groups at once first, which is one query and the common case. If
  // that is unsatisfiable then some group really is pinned together, and the
  // groups are taken one at a time, biggest first, each tried alongside the
  // ones already accepted. The budget keeps a query with very many groups
  // from turning into very many calls.
  size_t base = assumps.size();
  std::vector<Node> accepted;
  if (trySeparate(assumps, base, wanted))
  {
    accepted = wanted;
  }
  else
  {
    std::stable_sort(wanted.begin(), wanted.end(), [](TNode a, TNode b) {
      return a.getNumChildren() > b.getNumChildren();
    });
    size_t budget = s_maxSeparateCalls;
    for (const Node& w : wanted)
    {
      if (budget == 0)
      {
        break;
      }
      --budget;
      std::vector<Node> trial = accepted;
      trial.push_back(w);
      if (trySeparate(assumps, base, trial))
      {
        accepted = trial;
      }
    }
  }
  bool separatedAll = accepted.size() == wanted.size();
  // The last query may have been one that failed, so the separating model has
  // to be asked for again before the caller reads values from it.
  if (!accepted.empty() && trySeparate(assumps, base, accepted))
  {
    for (const Node& w : accepted)
    {
      d_ctx.getStats().d_numSeparatedEqs += w.getNumChildren();
    }
    return separatedAll;
  }
  // Nothing could be separated, or the separating model was lost. The caller
  // restores a model of the assumptions alone before reading values from it;
  // the equalities that remain are then genuinely worth deciding.
  d_haveModel = false;
  return false;
}

void Cvc5Bridge::restoreModel(std::vector<Node>& assumps)
{
  if (d_haveModel)
  {
    return;
  }
  // The queries the separation and propagation steps make can leave the
  // subsolver in an unsatisfiable state, and the caller needs a model of the
  // assumptions alone to read values from.
  Result r;
  try
  {
    r = checkSub(assumps);
  }
  catch (const std::exception&)
  {
    r = Result();
  }
  d_ctx.getStats().d_numBridgeChecks++;
  d_haveModel = r.getStatus() == Result::SAT;
}

bool Cvc5Bridge::propagateFixedGroup(std::vector<Node>& assumps,
                                     const std::vector<ENode*>& members,
                                     TNode val)
{
  // One query decides the whole group: the disjunction of the disequalities
  // is unsatisfiable exactly when every member is pinned to val, and then the
  // unsat assumptions justify each of the equalities in the conjunction.
  NodeManager* nm = d_ctx.getEnv().getNodeManager();
  std::vector<Node> diseqs;
  for (ENode* e : members)
  {
    diseqs.push_back(abstract(e->getExpr()).eqNode(val).notNode());
  }
  Node query =
      diseqs.size() == 1 ? diseqs[0] : nm->mkNode(Kind::OR, diseqs);
  size_t base = assumps.size();
  assumps.push_back(query);
  Result r;
  try
  {
    r = checkSub(assumps);
  }
  catch (const std::exception&)
  {
    assumps.resize(base);
    return false;
  }
  d_ctx.getStats().d_numBridgeChecks++;
  d_haveModel = r.getStatus() == Result::SAT;
  if (r.getStatus() != Result::UNSAT)
  {
    assumps.resize(base);
    return false;
  }
  LiteralVector lits;
  ENodePairVector eqs;
  bool ok = true;
  for (const Node& a : unsatCore())
  {
    if (a == query)
    {
      continue;
    }
    auto it = d_antecedents.find(a);
    if (it == d_antecedents.end())
    {
      ok = false;
      break;
    }
    if (it->second.d_eq.first != nullptr)
    {
      eqs.push_back(it->second.d_eq);
    }
    else
    {
      lits.push_back(it->second.d_lit);
    }
  }
  assumps.resize(base);
  if (!ok)
  {
    return false;
  }
  // Merging the term with the numeral is the point: it is what puts the
  // numeral's enode in the congruence closure and makes a pattern like
  // (uInv 32 0) or (Add 8 0) match, which is how Z3 reaches the instances
  // that close these queries. Z3 gets the same merges for free, from its
  // simplex noticing that a variable's bounds have met.
  bool propagated = false;
  for (ENode* e : members)
  {
    if (d_ctx.inconsistent())
    {
      break;
    }
    d_ctx.internalize(val, false);
    if (!d_ctx.eInternalized(val))
    {
      continue;
    }
    ENode* ec = d_ctx.getENode(val);
    if (ec->getRoot() == e->getRoot())
    {
      continue;
    }
    Trace("z3-bridge") << "cvc5 bridge: fixed " << e->getExpr() << " = " << val
                       << std::endl;
    d_ctx.getStats().d_numPropagatedEqs++;
    Justification* js =
        d_ctx.mkJustification(ExtTheoryEqPropagationJustification(
            theory::THEORY_ARITH,
            d_ctx,
            lits.size(),
            lits.data(),
            eqs.size(),
            eqs.data(),
            e,
            ec));
    d_ctx.assignEq(e, ec, EqJustification(js));
    propagated = true;
  }
  return propagated;
}

bool Cvc5Bridge::propagateFixedEqs(std::vector<Node>& assumps)
{
  if (!d_haveModel)
  {
    return false;
  }
  // Group the relevant bridged terms by the constant the model gives them.
  // Only a value two different congruence classes share is worth a query: an
  // equality is only worth anything if it merges two classes, or merges one
  // with the numeral itself.
  std::vector<std::pair<ENode*, Node>> shared;
  collectSharedRoots(shared);
  std::map<Node, std::vector<ENode*>> byValue;
  for (const std::pair<ENode*, Node>& p : shared)
  {
    if (p.second.isConst())
    {
      byValue[p.second].push_back(p.first);
    }
  }
  bool propagated = false;
  size_t budget = s_maxFixedCalls;
  for (const std::pair<const Node, std::vector<ENode*>>& g : byValue)
  {
    if (budget == 0 || d_ctx.inconsistent())
    {
      break;
    }
    // A single member still matters when the numeral's own enode is not in
    // the group: merging it with the numeral is what creates that enode.
    if (g.second.empty())
    {
      continue;
    }
    --budget;
    if (propagateFixedGroup(assumps, g.second, g.first))
    {
      propagated = true;
    }
  }
  return propagated;
}

FinalCheckStatus Cvc5Bridge::assumeInterfaceEqs()
{
  if (!d_haveModel)
  {
    // Without a model there is no way to tell whether the two solvers agree
    // on the shared terms, so no claim is made.
    d_ctx.markModelUnsound(theory::THEORY_ARITH);
    return FC_DONE;
  }
  bool result = false;
  for (TheoryCvc5* th : d_theories)
  {
    if (th->assumeInterfaceEqs())
    {
      result = true;
    }
  }
  return result ? FC_CONTINUE : FC_DONE;
}

// ------------------------------------------------------- per-theory facade

TheoryCvc5::TheoryCvc5(SmtContext& ctx, TheoryId tid, Cvc5Bridge& bridge)
    : Theory(ctx, tid), d_bridge(bridge)
{
  bridge.addTheory(this);
}

ENode* TheoryCvc5::getRepENode(TheoryVar v)
{
  ENode* r = getENode(v)->getRoot();
  TheoryVar rv = r->getThVar(getId());
  return rv == s_nullTheoryVar ? nullptr : getENode(rv);
}

namespace {

/**
 * The table Theory::assumeEqs needs: it groups the theory variables by the
 * value the subsolver's model gives them, which is how Z3's arithmetic solver
 * decides which interface equalities to assume (theory_arith's
 * m_var_value_table).
 */
class ModelValueTable
{
 public:
  ModelValueTable(Cvc5Bridge& bridge, TheoryCvc5& th)
      : d_bridge(bridge), d_th(th)
  {
  }

  void reset() { d_map.clear(); }

  TheoryVar insertIfNotThere(TheoryVar v)
  {
    Node val = d_bridge.getModelValue(d_th.getENode(v)->getExpr());
    if (val.isNull())
    {
      return v;
    }
    auto it = d_map.find(val);
    if (it != d_map.end())
    {
      return it->second;
    }
    d_map[val] = v;
    return v;
  }

 private:
  Cvc5Bridge& d_bridge;
  TheoryCvc5& d_th;
  std::unordered_map<Node, TheoryVar> d_map;
};

}  // namespace

bool TheoryCvc5::assumeInterfaceEqs()
{
  if (TraceIsOn("z3-bridge-share"))
  {
    size_t numShared = 0;
    size_t numValued = 0;
    size_t num = getNumVars();
    for (size_t v = 0; v < num; ++v)
    {
      ENode* n = getENode(static_cast<TheoryVar>(v));
      if (n == nullptr || !getContext().isRelevant(n)
          || !getContext().isShared(n))
      {
        continue;
      }
      numShared++;
      if (!d_bridge.getModelValue(n->getExpr()).isNull())
      {
        numValued++;
      }
    }
    Trace("z3-bridge-share") << "assume_eqs: " << num << " vars, "
                             << numShared << " relevant+shared, " << numValued
                             << " with a value" << std::endl;
  }
  ModelValueTable table(d_bridge, *this);
  return assumeEqs(table);
}

bool TheoryCvc5::internalizeAtom(TNode atom, bool /*gateCtx*/)
{
  forcePush();
  SmtContext& ctx = getContext();
  for (const Node& arg : atom)
  {
    ctx.internalize(arg, false);
  }
  if (ctx.bInternalized(atom))
  {
    return true;
  }
  BoolVar v = ctx.mkBoolVar(atom);
  ctx.setVarTheory(v, getId());
  d_bridge.registerAtom(atom, v);
  return true;
}

void TheoryCvc5::internalizeEqEh(TNode atom, BoolVar v)
{
  // An equality between terms of a bridged sort is internalized by the core,
  // which does the congruence reasoning; the subsolver needs it too.
  d_bridge.registerAtom(atom, v);
}

bool TheoryCvc5::internalizeTerm(TNode term)
{
  forcePush();
  SmtContext& ctx = getContext();
  for (const Node& arg : term)
  {
    ctx.internalize(arg, false);
  }
  if (ctx.eInternalized(term))
  {
    ENode* e = ctx.getENode(term);
    if (!isAttachedToVar(e))
    {
      mkVar(e);
      d_bridge.registerTerm(term);
    }
    return true;
  }
  ENode* e = ctx.mkENode(term,
                         false, /* the arguments take part in congruence */
                         false, /* a term, so it is not merged with true */
                         true /* congruence closure is enabled */);
  mkVar(e);
  d_bridge.registerTerm(term);
  return true;
}

TheoryVar TheoryCvc5::mkVar(ENode* n)
{
  TheoryVar v = Theory::mkVar(n);
  getContext().attachThVar(n, this, v);
  return v;
}

void TheoryCvc5::applySortCnstr(ENode* n, const TypeNode& /*s*/)
{
  forcePush();
  // Every term of a bridged sort has to take part in the interface, since the
  // core may merge it with one the bridge created.
  if (!isAttachedToVar(n))
  {
    mkVar(n);
    d_bridge.registerTerm(n->getExpr());
  }
}

FinalCheckStatus TheoryCvc5::finalCheckEh(size_t /*level*/)
{
  forcePush();
  if (!d_bridge.isOwner(this))
  {
    // One subsolver call covers every bridged theory at once.
    return FC_DONE;
  }
  return d_bridge.check(true);
}

bool TheoryCvc5::canPropagate()
{
  return getParams().d_bridgeEager && d_bridge.isOwner(this)
         && d_bridge.shouldCheckEagerly();
}

void TheoryCvc5::propagate()
{
  if (!getParams().d_bridgeEager || !d_bridge.isOwner(this))
  {
    return;
  }
  d_bridge.check(false);
}

void TheoryCvc5::resetEh()
{
  Theory::resetEh();
  if (d_bridge.isOwner(this))
  {
    d_bridge.reset();
  }
}

Theory* mkTheoryArithBridge(SmtContext& ctx)
{
  return new TheoryCvc5(ctx, theory::THEORY_ARITH, ctx.getCvc5Bridge());
}

Theory* mkTheoryBvBridge(SmtContext& ctx)
{
  return new TheoryCvc5(ctx, theory::THEORY_BV, ctx.getCvc5Bridge());
}

}  // namespace z3
}  // namespace cvc5::internal
