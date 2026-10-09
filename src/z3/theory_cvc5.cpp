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
    r = d_sub->checkSat(assumps);
  }
  catch (const std::exception& e)
  {
    Trace("z3") << "cvc5 bridge: the subsolver failed: " << e.what()
                << std::endl;
    d_ctx.markModelUnsound(theory::THEORY_ARITH);
    return FC_DONE;
  }
  d_ctx.getStats().d_numBridgeChecks++;
  if (r.getStatus() == Result::SAT)
  {
    // The two solvers agree on the literals. Their models still have to agree
    // on the terms they share, which is what the interface equalities below
    // establish.
    FinalCheckStatus st = checkInterface(assumps, finalCheck);
    if (st == FC_DONE)
    {
      if (d_satSets.size() < s_maxCachedSatSets)
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
  std::vector<Node> core = d_sub->getUnsatAssumptions();
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

Node Cvc5Bridge::mkAbsConst(TNode t)
{
  SkolemManager* sm = d_ctx.getEnv().getNodeManager()->getSkolemManager();
  return sm->mkDummySkolem("z3abs", t.getType());
}

bool Cvc5Bridge::isBridged(TheoryId tid)
{
  return tid == theory::THEORY_ARITH || tid == theory::THEORY_BV;
}

bool Cvc5Bridge::isSharedClass(ENode* r)
{
  // The class is shared if any member, or any parent of a member, belongs to
  // a theory the subsolver does not own: then both solvers constrain the
  // value of the class and their models have to agree on it.
  ENode* n = r;
  do
  {
    if (!isBridged(familyIdOf(n->getExpr())))
    {
      return true;
    }
    for (ENode* p : n->getConstParents())
    {
      if (!isBridged(familyIdOf(p->getExpr())))
      {
        return true;
      }
    }
    n = n->getNext();
  } while (n != r);
  return false;
}

bool Cvc5Bridge::shouldCheckEagerly() const
{
  return d_ctx.getStats().d_numAssignments >= d_lastCheckAssignments + d_eagerGap;
}

FinalCheckStatus Cvc5Bridge::checkInterface(std::vector<Node>& assumps,
                                            bool finalCheck)
{
  // Two shared classes the subsolver gives the same value but that the core
  // keeps apart are the one case where the two models may be incompatible.
  // For each such pair, ask the subsolver whether the two have to be equal:
  // if they do, the equality is propagated to the core -- which is what Z3's
  // own arithmetic solver does, and what lets E-matching see the terms the
  // bridged theory identified. If they do not, the disequality is assumed and
  // the next model is examined.
  size_t numExtra = 0;
  size_t extraBase = assumps.size();
  size_t budget =
      finalCheck ? s_maxInterfaceChecks : s_maxEagerInterfaceChecks;
  for (;;)
  {
    std::vector<std::pair<ENode*, ENode*>> candidates;
    collectCandidates(candidates);
    Trace("z3-bridge") << "cvc5 bridge: " << candidates.size()
                       << " interface candidates" << std::endl;
    if (candidates.empty())
    {
      // The last model of the subsolver agrees with the core on every shared
      // class, so the two models can be combined.
      assumps.resize(extraBase);
      return FC_DONE;
    }
    if (numExtra >= budget)
    {
      assumps.resize(extraBase);
      if (!finalCheck)
      {
        // Outside a final check there is nothing that has to be reconciled.
        return FC_DONE;
      }
      // Too many rounds: fall back to splitting on the first candidate and
      // let the search decide it.
      ENode* n1 = candidates.front().first;
      ENode* n2 = candidates.front().second;
      return mkInterfaceSplit(n1, n2);
    }
    ENode* n1 = candidates.front().first;
    ENode* n2 = candidates.front().second;
    Node diseq = abstract(n1->getExpr())
                     .eqNode(abstract(n2->getExpr()))
                     .notNode();
    Trace("z3-bridge-if") << "  try " << n1->getExpr() << " = "
                          << n2->getExpr() << std::endl;
    assumps.push_back(diseq);
    numExtra++;
    Result r;
    try
    {
      r = d_sub->checkSat(assumps);
    }
    catch (const std::exception&)
    {
      assumps.resize(extraBase);
      d_ctx.markModelUnsound(theory::THEORY_ARITH);
      return FC_DONE;
    }
    d_ctx.getStats().d_numBridgeChecks++;
    if (r.getStatus() == Result::SAT)
    {
      // The two can be kept apart; keep the disequality and look at the new
      // model.
      Trace("z3-bridge-if") << "    not entailed" << std::endl;
      continue;
    }
    if (r.getStatus() != Result::UNSAT)
    {
      assumps.resize(extraBase);
      d_ctx.markModelUnsound(theory::THEORY_ARITH);
      return FC_DONE;
    }
    // The equality is entailed, so propagate it to the core.
    LiteralVector lits;
    ENodePairVector eqs;
    bool ok = true;
    for (const Node& a : d_sub->getUnsatAssumptions())
    {
      if (a == diseq)
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
    assumps.resize(extraBase);
    if (!ok)
    {
      // One of the assumed disequalities was used, so the equality only holds
      // relative to them: split instead of propagating.
      return mkInterfaceSplit(n1, n2);
    }
    Trace("z3-bridge") << "cvc5 bridge: propagate " << n1->getExpr() << " = "
                       << n2->getExpr() << std::endl;
    d_ctx.getStats().d_numInterfaceEqs++;
    Justification* js =
        d_ctx.mkJustification(ExtTheoryEqPropagationJustification(
            theory::THEORY_ARITH,
            d_ctx,
            lits.size(),
            lits.data(),
            eqs.size(),
            eqs.data(),
            n1,
            n2));
    d_ctx.assignEq(n1, n2, EqJustification(js));
    return FC_CONTINUE;
  }
}

void Cvc5Bridge::collectCandidates(
    std::vector<std::pair<ENode*, ENode*>>& candidates)
{
  // Every class takes part in the grouping by value, but a pair is only
  // proposed when at least one of the two is shared: the common case is a
  // term the subsolver fixed to a numeral, where the numeral's own class is
  // of no interest to the other solvers.
  std::unordered_map<Node, std::pair<ENode*, bool>> valueToRep;
  std::unordered_set<ENode*> seen;
  for (const Node& t : d_terms)
  {
    if (!d_ctx.eInternalized(t))
    {
      continue;
    }
    ENode* e = d_ctx.getENode(t);
    ENode* r = e->getRoot();
    if (!seen.insert(r).second)
    {
      continue;
    }
    Node at = abstract(t);
    if (d_known.count(at) == 0)
    {
      // The subsolver has never seen this term, so it does not constrain its
      // value and the core is free to choose one.
      continue;
    }
    Node val;
    try
    {
      // getValue warns when the model cannot evaluate the term, which here is
      // an expected outcome rather than a problem worth reporting.
      std::stringstream dropped;
      std::ostream* old = &WarningChannel.setStream(&dropped);
      try
      {
        val = d_sub->getValue(at);
      }
      catch (...)
      {
        WarningChannel.setStream(old);
        throw;
      }
      WarningChannel.setStream(old);
    }
    catch (const std::exception&)
    {
      // The subsolver does not constrain this term, so the core is free to
      // give it any value.
      continue;
    }
    if (val.isNull())
    {
      continue;
    }
    bool shared = isSharedClass(r);
    auto it = valueToRep.find(val);
    if (it == valueToRep.end())
    {
      valueToRep[val] = std::pair<ENode*, bool>(e, shared);
      continue;
    }
    if (it->second.first->getRoot() == r)
    {
      continue;
    }
    if (!shared && !it->second.second)
    {
      continue;
    }
    candidates.push_back(std::pair<ENode*, ENode*>(it->second.first, e));
  }
}

FinalCheckStatus Cvc5Bridge::mkInterfaceSplit(ENode* n1, ENode* n2)
{
  Node eq = d_ctx.mkEqAtom(n1->getExpr(), n2->getExpr());
  if (d_ctx.bInternalized(eq) && d_ctx.getAssignment(eq) != L_UNDEF)
  {
    // The search already decided this equality, so splitting on it again
    // would not make progress.
    d_ctx.markModelUnsound(theory::THEORY_ARITH);
    return FC_DONE;
  }
  Trace("z3-bridge") << "cvc5 bridge: interface split " << eq << std::endl;
  d_ctx.getStats().d_numInterfaceEqs++;
  d_ctx.internalize(eq, true);
  d_ctx.markAsRelevant(d_ctx.getBoolVar(eq));
  return FC_CONTINUE;
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
