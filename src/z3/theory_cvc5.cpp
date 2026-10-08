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
#include <sstream>
#include <unordered_set>

#include "base/output.h"
#include "options/base_options.h"
#include "options/option_exception.h"
#include "options/smt_options.h"
#include "options/z3_options.h"
#include "smt/env.h"
#include "smt/set_defaults.h"
#include "smt/solver_engine.h"
#include "theory/smt_engine_subsolver.h"
#include "util/result.h"
#include "z3/ast.h"
#include "z3/justification.h"
#include "z3/smt_context.h"

namespace cvc5::internal {
namespace z3 {

// ----------------------------------------------------------------- bridge

Cvc5Bridge::Cvc5Bridge(SmtContext& ctx) : d_ctx(ctx), d_subFailed(false) {}

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
    Node lit = val == L_TRUE ? ab.first : ab.first.notNode();
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
    Node eq = it->second->getExpr().eqNode(e->getExpr());
    if (d_antecedents.count(eq) != 0)
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
  // Only the terms that occur in an assumption are known to the subsolver;
  // asking for the value of any other one is pointless and noisy.
  d_known.clear();
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

FinalCheckStatus Cvc5Bridge::check()
{
  if (d_atoms.empty() && d_terms.empty())
  {
    return FC_DONE;
  }
  if (!initSubsolver())
  {
    d_ctx.markModelUnsound(theory::THEORY_ARITH);
    return FC_DONE;
  }
  std::vector<Node> assumps;
  mkAssumptions(assumps);
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
    return checkInterface(assumps);
  }
  if (r.getStatus() != Result::UNSAT)
  {
    d_ctx.markModelUnsound(theory::THEORY_ARITH);
    return FC_DONE;
  }
  d_ctx.getStats().d_numBridgeConflicts++;
  LiteralVector lits;
  ENodePairVector eqs;
  std::vector<Node> core = d_sub->getUnsatAssumptions();
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
  return FC_CONTINUE;
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

FinalCheckStatus Cvc5Bridge::checkInterface(std::vector<Node>& assumps)
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
    if (numExtra >= s_maxInterfaceChecks)
    {
      // Too many rounds: fall back to splitting on the first candidate and
      // let the search decide it.
      ENode* n1 = candidates.front().first;
      ENode* n2 = candidates.front().second;
      assumps.resize(extraBase);
      return mkInterfaceSplit(n1, n2);
    }
    ENode* n1 = candidates.front().first;
    ENode* n2 = candidates.front().second;
    Node diseq = d_ctx.mkEqAtom(n1->getExpr(), n2->getExpr()).notNode();
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
    if (d_known.count(t) == 0)
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
        val = d_sub->getValue(t);
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
  return d_bridge.check();
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
