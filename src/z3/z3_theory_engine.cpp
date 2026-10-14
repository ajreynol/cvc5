/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory engine of the ported Z3 core.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "z3/z3_theory_engine.h"

#include "base/output.h"
#include "expr/node_algorithm.h"
#include "proof/trust_node.h"
#include "prop/prop_engine.h"
#include "smt/env.h"
#include "theory/incomplete_id.h"
#include "theory/inference_id.h"
#include "z3/prop_core.h"
#include "z3/smt_context.h"

namespace cvc5::internal {
namespace z3 {

namespace {

/**
 * How many times in a row a full check retries the final check of the
 * theory side when it asks to continue without telling cvc5 anything new.
 */
constexpr size_t s_maxSilentFinalChecks = 10;

}  // namespace

Z3TheoryEngine::Z3TheoryEngine(Env& env, bool hosted)
    : TheoryEngine(env),
      d_backend(env),
      d_hosted(hosted),
      d_setup(false),
      d_conflictSent(false),
      d_needCheck(false),
      d_reportIdx(0)
{
  if (d_hosted)
  {
    d_popNotify = std::make_unique<PopNotify>(context(), *this);
  }
}

Z3TheoryEngine::~Z3TheoryEngine() {}

void Z3TheoryEngine::hostReset()
{
  d_setup = false;
  d_conflictSent = false;
  d_needCheck = false;
  d_propagations.clear();
  d_reportIdx = 0;
  d_preregistered.clear();
  d_lemmasSent.clear();
}

void Z3TheoryEngine::preRegister(TNode atom)
{
  if (!d_hosted)
  {
    TheoryEngine::preRegister(atom);
    return;
  }
  // The atoms of the input are internalized with the asserted formulas when
  // the search starts; the others are internalized at the next check.
  Trace("z3-host") << "preregister " << atom << std::endl;
  if (d_setup)
  {
    d_preregistered.push_back(atom);
  }
}

void Z3TheoryEngine::assertFact(TNode literal)
{
  if (!d_hosted)
  {
    TheoryEngine::assertFact(literal);
    return;
  }
  if (d_conflictSent)
  {
    return;
  }
  PropCore& core = d_backend.getPropCore();
  core.hostSyncLevel(context()->getLevel());
  Trace("z3-host") << "assert " << literal << std::endl;
  Literal l = core.hostLiteral(literal);
  std::vector<Literal> conflict;
  if (!core.hostAssign(l, conflict))
  {
    sendConflict(conflict);
  }
}

void Z3TheoryEngine::check(theory::Theory::Effort effort)
{
  if (!d_hosted)
  {
    TheoryEngine::check(effort);
    return;
  }
  d_needCheck = false;
  // cvc5 has taken the propagations of the previous check
  d_propagations.clear();
  Trace("z3-host") << "check " << effort << " at level "
                   << context()->getLevel() << " conflictSent "
                   << d_conflictSent << std::endl;
  if (d_conflictSent)
  {
    // The conflict sent in this context has not made cvc5 backtrack. A
    // full check must then not let the model through.
    if (theory::Theory::fullEffort(effort))
    {
      setModelUnsound(theory::IncompleteId::UNKNOWN);
    }
    return;
  }
  PropCore& core = d_backend.getPropCore();
  core.hostSyncLevel(context()->getLevel());
  for (const Node& atom : d_preregistered)
  {
    core.hostLiteral(atom);
  }
  d_preregistered.clear();
  if (!propagateAndReport())
  {
    return;
  }
  if (!theory::Theory::fullEffort(effort) || d_needCheck
      || !d_propagations.empty())
  {
    Trace("z3-host") << "check returns: needCheck " << d_needCheck
                     << " propagations " << d_propagations.size() << std::endl;
    return;
  }
  for (size_t i = 0; i < s_maxSilentFinalChecks; ++i)
  {
    Failure f = OK;
    FinalCheckStatus st = core.hostFinalCheck(f);
    Trace("z3-host") << "final check " << st << " at level "
                     << context()->getLevel() << std::endl;
    if (st == FC_GIVEUP)
    {
      setModelUnsound(theory::IncompleteId::UNKNOWN);
      return;
    }
    if (st == FC_DONE)
    {
      // The core's own search reaches a final check only once every relevant
      // variable is assigned, while cvc5 may stop on a partial assignment.
      // The relevant variables left are decided first, through splitting
      // lemmas that cvc5's decision heuristic must justify.
      splitPendingAtoms();
      if (d_needCheck)
      {
        return;
      }
      std::string reason;
      if (d_backend.getContext().hasQuantifiers())
      {
        setModelUnsound(theory::IncompleteId::QUANTIFIERS);
      }
      else if (!d_backend.getContext().canConfirmModel(reason))
      {
        setModelUnsound(theory::IncompleteId::UNKNOWN);
      }
      return;
    }
    // FC_CONTINUE: the theory side made progress
    if (!propagateAndReport())
    {
      return;
    }
    splitPendingAtoms();
    if (d_needCheck || !d_propagations.empty())
    {
      return;
    }
  }
  setModelUnsound(theory::IncompleteId::UNKNOWN);
}

bool Z3TheoryEngine::presolve()
{
  if (!d_hosted)
  {
    return TheoryEngine::presolve();
  }
  if (!d_setup)
  {
    d_backend.getPropCore().hostInit();
    d_setup = true;
  }
  return false;
}

void Z3TheoryEngine::postsolve(prop::SatValue result)
{
  if (!d_hosted)
  {
    TheoryEngine::postsolve(result);
  }
}

void Z3TheoryEngine::notifyRestart()
{
  if (!d_hosted)
  {
    TheoryEngine::notifyRestart();
  }
}

void Z3TheoryEngine::getPropagatedLiterals(std::vector<TNode>& literals)
{
  if (!d_hosted)
  {
    TheoryEngine::getPropagatedLiterals(literals);
    return;
  }
  // d_propagations keeps the nodes alive until the next check
  literals.insert(literals.end(), d_propagations.begin(), d_propagations.end());
}

Node Z3TheoryEngine::getNextDecisionRequest()
{
  if (!d_hosted)
  {
    return TheoryEngine::getNextDecisionRequest();
  }
  return Node::null();
}

TrustNode Z3TheoryEngine::getExplanation(TNode literal)
{
  if (!d_hosted)
  {
    return TheoryEngine::getExplanation(literal);
  }
  PropCore& core = d_backend.getPropCore();
  Literal l = core.hostLiteral(literal);
  Assert(core.getAssignment(l) == L_TRUE);
  std::vector<Literal> lits;
  core.hostExplain(l, lits);
  NodeManager* nm = nodeManager();
  Node exp;
  if (lits.empty())
  {
    exp = nm->mkConst(true);
  }
  else if (lits.size() == 1)
  {
    exp = literalNode(lits[0]);
  }
  else
  {
    std::vector<Node> conj;
    for (Literal a : lits)
    {
      conj.push_back(literalNode(a));
    }
    exp = nm->mkNode(Kind::AND, conj);
  }
  return TrustNode::mkTrustPropExp(literal, exp, nullptr);
}

bool Z3TheoryEngine::needCheck() const
{
  if (!d_hosted)
  {
    return TheoryEngine::needCheck();
  }
  return d_needCheck;
}

void Z3TheoryEngine::notifyPop()
{
  if (!d_setup)
  {
    return;
  }
  PropCore& core = d_backend.getPropCore();
  uint32_t lvl = context()->getLevel();
  if (core.getScopeLevel() > lvl)
  {
    core.hostSyncLevel(lvl);
  }
  d_conflictSent = false;
  size_t size = core.assignedLiterals().size();
  if (d_reportIdx > size)
  {
    d_reportIdx = size;
  }
}

void Z3TheoryEngine::sendConflict(const std::vector<Literal>& lits)
{
  NodeManager* nm = nodeManager();
  std::vector<Node> disj;
  for (Literal l : lits)
  {
    disj.push_back(literalNode(~l));
  }
  Node lem = disj.empty()       ? nm->mkConst(false)
             : disj.size() == 1 ? disj[0]
                                : nm->mkNode(Kind::OR, disj);
  getPropEngine()->assertLemmaUnprocessed(theory::InferenceId::UNKNOWN,
                                          TrustNode::mkTrustLemma(lem),
                                          theory::LemmaProperty::NONE);
  d_conflictSent = true;
  d_needCheck = true;
}

void Z3TheoryEngine::sendLemmas()
{
  std::vector<Node> lems;
  d_backend.getPropCore().hostTakeLemmas(lems);
  for (const Node& lem : lems)
  {
    // cvc5 keeps its lemmas, while the core makes an instance or an axiom
    // again after backtracking
    if (!d_lemmasSent.insert(lem).second)
    {
      continue;
    }
    getPropEngine()->assertLemmaUnprocessed(theory::InferenceId::UNKNOWN,
                                            TrustNode::mkTrustLemma(lem),
                                            theory::LemmaProperty::NONE);
    d_needCheck = true;
  }
}

void Z3TheoryEngine::collectPropagations()
{
  PropCore& core = d_backend.getPropCore();
  const LiteralVector& assigned = core.assignedLiterals();
  prop::PropEngine* pe = getPropEngine();
  if (d_reportIdx > assigned.size())
  {
    d_reportIdx = assigned.size();
  }
  for (; d_reportIdx < assigned.size(); ++d_reportIdx)
  {
    Literal l = assigned[d_reportIdx];
    BoolVar v = l.var();
    if (core.isHostAssigned(v))
    {
      continue;
    }
    TNode atom = core.boolVar2Expr(v);
    if (atom.isNull() || atom.isConst() || expr::isBooleanConnective(atom)
        || !pe->isSatLiteral(atom))
    {
      continue;
    }
    d_propagations.push_back(literalNode(l));
  }
}

void Z3TheoryEngine::splitPendingAtoms()
{
  PropCore& core = d_backend.getPropCore();
  prop::PropEngine* pe = getPropEngine();
  NodeManager* nm = nodeManager();
  for (size_t i = 0, n = core.getNumBoolVars(); i < n; ++i)
  {
    BoolVar v = static_cast<BoolVar>(i);
    TNode atom = core.boolVar2Expr(v);
    if (atom.isNull() || atom.isConst() || core.getAssignment(v) != L_UNDEF
        || !core.isRelevant(v))
    {
      continue;
    }
    Node lem = nm->mkNode(Kind::OR, atom, atom.notNode());
    Trace("z3-host") << "split " << atom << std::endl;
    if (!d_lemmasSent.insert(lem).second)
    {
      continue;
    }
    getPropEngine()->assertLemmaUnprocessed(theory::InferenceId::UNKNOWN,
                                            TrustNode::mkTrustLemma(lem),
                                            theory::LemmaProperty::NONE);
    // cvc5's preprocessing of the lemma may have rewritten the atom
    if (core.tryTrueFirst(v) && pe->isSatLiteral(atom))
    {
      pe->preferPhase(atom, true);
    }
    d_needCheck = true;
  }
}

bool Z3TheoryEngine::propagateAndReport()
{
  PropCore& core = d_backend.getPropCore();
  bool ok = core.hostPropagate();
  // the instances and axioms made before a conflict hold regardless
  sendLemmas();
  if (!ok)
  {
    std::vector<Literal> conflict;
    core.hostExplainConflict(conflict);
    sendConflict(conflict);
    return false;
  }
  collectPropagations();
  return true;
}

Node Z3TheoryEngine::literalNode(Literal l)
{
  return d_backend.getPropCore().literal2Expr(l);
}

}  // namespace z3
}  // namespace cvc5::internal
