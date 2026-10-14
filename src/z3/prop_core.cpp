/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The Boolean search of the ported Z3 core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), the
 * Boolean part of files src/smt/smt_context.cpp and
 * src/smt/smt_internalizer.cpp, and recast in cvc5 style.
 */

#include "z3/prop_core.h"

#include <algorithm>
#include <unordered_set>

#include "base/output.h"
#include "expr/node_algorithm.h"
#include "expr/node_manager.h"
#include "options/z3_options.h"
#include "smt/env.h"
#include "util/resource_manager.h"
#include "z3/conflict_resolution.h"
#include "z3/quantifier_manager.h"
#include "z3/smt_context.h"
#include "z3/theory.h"
#include "z3/util/luby.h"
#include "z3/util/uint_set.h"

namespace cvc5::internal {
namespace z3 {

std::ostream& operator<<(std::ostream& out, Failure f)
{
  switch (f)
  {
    case OK: out << "ok"; break;
    case UNKNOWN: out << "unknown"; break;
    case MEMOUT: out << "memout"; break;
    case CANCELED: out << "canceled"; break;
    case NUM_CONFLICTS: out << "num-conflicts"; break;
    case THEORY: out << "theory"; break;
    case RESOURCE_LIMIT: out << "resource-limit"; break;
    case QUANTIFIERS: out << "quantifiers"; break;
  }
  return out;
}

namespace {

bool isTrueNode(TNode n)
{
  return n.getKind() == Kind::CONST_BOOLEAN && n.getConst<bool>();
}

bool isFalseNode(TNode n)
{
  return n.getKind() == Kind::CONST_BOOLEAN && !n.getConst<bool>();
}

/** True if n is an atom or the negation of one, as Z3's is_literal is. */
bool isLiteralNode(TNode n)
{
  TNode a = n.getKind() == Kind::NOT ? n[0] : n;
  return !isApp(a) || a.getNumChildren() == 0;
}

}  // namespace

PropCore::PropCore(Env& env, SmtContext& ctx, Params& params, Statistics& stats)
    : EnvObj(env),
      d_ctx(ctx),
      d_params(params),
      d_stats(stats),
      d_relevancyLvl(params.d_relevancyLvl),
      d_relevancyPropagator(new RelevancyPropagator(*this, ctx)),
      d_qhead(0),
      d_simpQhead(0),
      d_simpCounter(0),
      d_caseSplitQueue(nullptr),
      d_bvarInc(1.0),
      d_phaseCacheOn(true),
      d_phaseCounter(0),
      d_phaseDefault(false),
      d_agility(0.0),
      d_conflict(s_nullBJustification),
      d_notL(s_nullLiteral),
      d_assertedInconsistent(false),
      d_flushing(false),
      d_assertedFormulasQhead(0),
      d_hasQuantifiers(false),
      d_internalizingAssertions(false),
      d_unknown("unknown"),
      d_conflictResolution(nullptr),
      d_lastSearchFailure(OK),
      d_searching(false),
      d_interrupted(false),
      d_numConflicts(0),
      d_numConflictsSinceRestart(0),
      d_numConflictsSinceLemmaGc(0),
      d_numRestarts(0),
      d_restartThreshold(params.d_restartInitial),
      d_restartOuterThreshold(params.d_restartInitial),
      d_lubyIdx(1),
      d_lemmaGcThreshold(params.d_lemmaGcInitial),
      d_scopeLvl(0),
      d_baseLvl(0),
      d_searchLvl(0),
      d_mkBoolVarTrail(*this)
{
}

PropCore::~PropCore() {}

void PropCore::finishInit()
{
  d_conflictResolution.reset(mkConflictResolution(
      *this, d_ctx.getExplainer(), d_params, d_assignedLiterals));
  d_caseSplitQueue.reset(mkCaseSplitQueue(*this, d_params));
}

void PropCore::initTrue(TNode t)
{
  mkBoolVar(t);
  Assert(getBoolVar(t) == s_trueBoolVar);
  Assert(s_trueLiteral.var() == s_trueBoolVar);
  d_assignment[s_trueLiteral.index()] = L_TRUE;
  d_assignment[s_falseLiteral.index()] = L_FALSE;
  d_bdata[s_trueBoolVar].setAxiom();
}

void PropCore::flushClauses()
{
  d_flushing = true;
  delClauses(d_auxClauses, 0);
  delClauses(d_lemmas, 0);
  d_flushing = false;
}

// ---------------------------------------------------- input and entry points

void PropCore::assertFormula(TNode e)
{
  if (getCancelFlag())
  {
    return;
  }
  if (!isSearching())
  {
    popToBaseLvl();
  }
  pushAssertion(e);
}

void PropCore::pushAssertion(TNode e)
{
  // Z3 splits a conjunction, and a negated disjunction, into separate
  // assertions while they are being collected (see
  // asserted_formulas::push_assertion). This matters beyond saving a Boolean
  // variable: an assertion is marked relevant when it is asserted, while the
  // conjuncts of a top-level conjunction never are -- the and-gate only
  // propagates relevancy to its arguments once the conjunction itself is
  // assigned, which never happens for a root. cvc5's preprocessor leaves
  // such conjunctions in place, so the split is done here.
  if (isTrueNode(e))
  {
    return;
  }
  if (isFalseNode(e))
  {
    d_assertedInconsistent = true;
    d_assertedFormulas.push_back(e);
    return;
  }
  if (e.getKind() == Kind::AND)
  {
    for (const Node& arg : e)
    {
      pushAssertion(arg);
    }
    return;
  }
  if (e.getKind() == Kind::NOT && e[0].getKind() == Kind::OR)
  {
    for (const Node& arg : e[0])
    {
      pushAssertion(arg.negate());
    }
    return;
  }
  // What Z3 does next is asserted_formulas::flatten_clauses, whose point is
  // that its core gets flat clauses rather than a tree of gates: every nested
  // gate costs a Boolean variable, two clauses and a link in the chain
  // relevancy has to walk before it reaches the atoms. A top-level
  // if-then-else is two clauses, and a top-level disjunction over a
  // conjunction distributes.
  if (e.getKind() == Kind::ITE)
  {
    pushAssertion(nodeManager()->mkNode(Kind::OR, e[0].negate(), e[1]));
    pushAssertion(nodeManager()->mkNode(Kind::OR, Node(e[0]), e[2]));
    return;
  }
  if (e.getKind() == Kind::OR && e.getNumChildren() == 2)
  {
    for (size_t i = 0; i < 2; ++i)
    {
      TNode conj = e[i];
      TNode rest = e[1 - i];
      // Z3 also distributes over a shared conjunction when the other side is
      // not a literal, using a reference count to tell that the conjunction
      // occurs nowhere else. There is no equally cheap test here, so only the
      // case that cannot grow the formula is taken: duplicating a literal
      // across the conjuncts costs one literal per conjunct.
      if (conj.getKind() == Kind::AND && isLiteralNode(rest))
      {
        for (const Node& arg : conj)
        {
          pushAssertion(nodeManager()->mkNode(Kind::OR, Node(rest), arg));
        }
        return;
      }
    }
  }
  if (!d_hasQuantifiers && expr::hasClosure(Node(e)))
  {
    d_hasQuantifiers = true;
  }
  Trace("z3-assert") << "ASSERT " << e << std::endl;
  d_assertedFormulas.push_back(e);
}

void PropCore::internalizeAssertions()
{
  if (getCancelFlag() || d_internalizingAssertions)
  {
    return;
  }
  d_internalizingAssertions = true;
  if (d_assertedInconsistent)
  {
    if (d_conflict == s_nullBJustification)
    {
      setConflict(BJustification::mkAxiom());
    }
    d_internalizingAssertions = false;
    return;
  }
  while (d_assertedFormulasQhead < d_assertedFormulas.size())
  {
    if (getCancelFlag())
    {
      d_internalizingAssertions = false;
      return;
    }
    TNode f = d_assertedFormulas[d_assertedFormulasQhead];
    ++d_assertedFormulasQhead;
    d_ctx.internalizeAssertion(f, 0);
  }
  d_internalizingAssertions = false;
}

bool PropCore::checkPreamble()
{
  d_stats.d_numChecks++;
  // The size of what the core is given, to be compared with the num-exprs
  // Z3 reports for the same query at verbosity 10.
  d_stats.d_numAssertedFormulas = d_assertedFormulas.size();
  std::unordered_set<TNode> seen;
  std::vector<TNode> todo(d_assertedFormulas.begin(), d_assertedFormulas.end());
  while (!todo.empty())
  {
    TNode n = todo.back();
    todo.pop_back();
    if (!seen.insert(n).second)
    {
      continue;
    }
    todo.insert(todo.end(), n.begin(), n.end());
  }
  d_stats.d_numAssertedExprs = seen.size();
  if (!d_env.getOptions().z3.z3DumpAssertions.empty())
  {
    d_ctx.dumpAssertions(d_env.getOptions().z3.z3DumpAssertions.c_str());
  }
  popToBaseLvl();
  resetConflictResolution();
  return true;
}

LBool PropCore::checkFinalize(LBool r)
{
  d_ctx.reportQuantifierProfile();

  if (r == L_TRUE && getCancelFlag())
  {
    r = L_UNDEF;
  }
  std::string reason;
  if (r == L_TRUE && !d_ctx.canConfirmModel(reason))
  {
    d_lastSearchFailure = THEORY;
    d_unknown = reason;
    r = L_UNDEF;
  }
  return r;
}

LBool PropCore::setupAndCheck() { return check(); }

LBool PropCore::check()
{
  if (!checkPreamble())
  {
    return L_UNDEF;
  }
  Assert(atBaseLevel());
  // The configuration happens on the first check only; passing autoConfig
  // here is what makes that first call collect the static features of the
  // input, as Z3 does when it is given a file rather than driven
  // incrementally.
  d_ctx.setupContext(d_params.d_autoConfig);
  popToBaseLvl();
  internalizeAssertions();
  // Z3 sets the search level in init_assumptions, which also creates the
  // scope the assumptions live in. This port does not support assumptions
  // (see the README), so the search level is simply the current scope.
  d_searchLvl = d_scopeLvl;
  Assert(getSearchLevel() == getBaseLevel());
  LBool r = search();
  return checkFinalize(r);
}

void PropCore::push()
{
  popToBaseLvl();
  d_ctx.setupContext(false);
  bool wasConsistent = !inconsistent();
  internalizeAssertions();
  propagate();
  if (wasConsistent && inconsistent() && !isAssertedInconsistent())
  {
    // the logical context became inconsistent during the user push
    bool resolved = resolveConflict();
    Assert(!resolved);
    (void)resolved;
  }
  pushScope();
  pushBaseScope();
}

void PropCore::pop(size_t numScopes)
{
  Assert(numScopes > 0);
  if (numScopes > d_scopeLvl)
  {
    return;
  }
  popToBaseLvl();
  popScope(numScopes);
}

// ------------------------------------------------------------- search driver

bool PropCore::getCancelFlag()
{
  if (d_interrupted)
  {
    d_lastSearchFailure = CANCELED;
    return true;
  }
  if (!resourceManager()->out())
  {
    return false;
  }
  d_lastSearchFailure =
      resourceManager()->outOfResources() ? RESOURCE_LIMIT : CANCELED;
  return true;
}

bool PropCore::resourceLimitsExceeded()
{
  if (d_searching && d_lastSearchFailure != OK)
  {
    return true;
  }
  return getCancelFlag();
}

void PropCore::resetConflictResolution() { d_conflictResolution->reset(); }

void PropCore::initSearch()
{
  d_ctx.initSearchEh();
  d_numConflicts = 0;
  d_numConflictsSinceRestart = 0;
  d_numConflictsSinceLemmaGc = 0;
  d_numRestarts = 0;
  d_restartThreshold = d_params.d_restartInitial;
  d_restartOuterThreshold = d_params.d_restartInitial;
  d_lubyIdx = 1;
  d_lemmaGcThreshold = d_params.d_lemmaGcInitial;
  d_lastSearchFailure = OK;
  d_agility = 0.0;
  d_phaseDefault = false;
  d_caseSplitQueue->initSearchEh();
}

void PropCore::endSearch() { d_caseSplitQueue->endSearchEh(); }

void PropCore::incLimits()
{
  if (d_numConflictsSinceRestart >= d_restartThreshold)
  {
    switch (d_params.d_restartStrategy)
    {
      case RS_GEOMETRIC:
        d_restartThreshold = static_cast<uint64_t>(
            static_cast<double>(d_restartThreshold) * d_params.d_restartFactor);
        break;
      case RS_IN_OUT_GEOMETRIC:
        d_restartThreshold = static_cast<uint64_t>(
            static_cast<double>(d_restartThreshold) * d_params.d_restartFactor);
        if (d_restartThreshold > d_restartOuterThreshold)
        {
          d_restartThreshold = d_params.d_restartInitial;
          d_restartOuterThreshold =
              static_cast<uint64_t>(static_cast<double>(d_restartOuterThreshold)
                                    * d_params.d_restartFactor);
        }
        break;
      case RS_LUBY:
        d_lubyIdx++;
        if (d_params.d_restartLubyFactor == 2.0)
        {
          d_restartThreshold = static_cast<uint64_t>(getLuby(d_lubyIdx))
                               * d_params.d_restartInitial;
        }
        else
        {
          // as MiniSat, whose sequence starts at index 0
          d_restartThreshold = static_cast<uint64_t>(
              getLuby(d_params.d_restartLubyFactor, d_lubyIdx - 1)
              * d_params.d_restartInitial);
        }
        break;
      case RS_FIXED: break;
      case RS_ARITHMETIC:
        d_restartThreshold = static_cast<uint64_t>(
            static_cast<double>(d_restartThreshold) + d_params.d_restartFactor);
        break;
    }
  }
  d_numConflictsSinceRestart = 0;
}

LBool PropCore::search()
{
  if (d_assertedInconsistent)
  {
    setConflict(BJustification::mkAxiom());
    return L_FALSE;
  }
  if (inconsistent())
  {
    bool resolved = resolveConflict();
    Assert(!resolved);
    (void)resolved;
    return L_FALSE;
  }
  if (getCancelFlag())
  {
    return L_UNDEF;
  }

  Assert(atSearchLevel());
  initSearch();

  d_searching = true;
  LBool status = L_UNDEF;
  uint32_t currLvl = d_scopeLvl;

  while (true)
  {
    Assert(!inconsistent());
    status = boundedSearch();
    if (!restart(status, currLvl))
    {
      break;
    }
  }

  endSearch();
  d_searching = false;
  return status;
}

bool PropCore::restart(LBool& status, uint32_t currLvl)
{
  Assert(status != L_TRUE || !inconsistent());

  if (d_lastSearchFailure != OK)
  {
    return false;
  }
  if (status == L_FALSE)
  {
    return false;
  }
  if (status == L_TRUE)
  {
    // The possible outcomes are: done sat, done unknown, or continue.
    switch (d_ctx.checkModel())
    {
      case QuantifierManager::SAT: return false;
      case QuantifierManager::UNKNOWN:
        // giving up
        d_lastSearchFailure = QUANTIFIERS;
        status = L_UNDEF;
        return false;
      default: break;
    }
  }
  Trace("z3-events") << "RESTART decisions " << d_stats.d_numDecisions
                     << " conflicts " << d_stats.d_numConflicts << std::endl;
  incLimits();
  if (status == L_TRUE || !d_params.d_restartAdaptive
      || d_agility < d_params.d_restartAgilityThreshold)
  {
    Assert(!inconsistent());
    // execute the restart
    d_stats.d_numRestarts++;
    d_numRestarts++;
    if (d_scopeLvl > currLvl)
    {
      popScope(d_scopeLvl - currLvl);
      Assert(atSearchLevel());
    }
    d_ctx.restartEh();
    if (inconsistent())
    {
      bool resolved = resolveConflict();
      Assert(!resolved);
      (void)resolved;
      status = L_FALSE;
      return false;
    }
    if (d_numRestarts >= d_params.d_restartMax)
    {
      status = L_UNDEF;
      d_lastSearchFailure = NUM_CONFLICTS;
      return false;
    }
  }
  if (d_params.d_simplifyClauses)
  {
    simplifyClauses();
  }
  if (d_params.d_lemmaGcStrategy == LGC_AT_RESTART)
  {
    delInactiveLemmas();
  }

  status = L_UNDEF;
  return true;
}

void PropCore::tick(uint32_t& counter) const
{
  counter++;
  if (counter > d_params.d_tick)
  {
    counter = 0;
  }
}

LBool PropCore::boundedSearch()
{
  uint32_t counter = 0;

  while (true)
  {
    while (!propagate())
    {
      tick(counter);

      if (!resolveConflict())
      {
        return L_FALSE;
      }

      Assert(d_scopeLvl >= d_baseLvl);

      if (!inconsistent())
      {
        if (resourceLimitsExceeded())
        {
          return L_UNDEF;
        }
        if (getCancelFlag())
        {
          return L_UNDEF;
        }
        if (d_numConflictsSinceRestart > d_restartThreshold
            && d_scopeLvl - d_baseLvl > 2)
        {
          return L_UNDEF;  // restart
        }
        if (d_numConflicts > d_params.d_maxConflicts)
        {
          d_lastSearchFailure = NUM_CONFLICTS;
          return L_UNDEF;
        }
      }

      if (d_numConflictsSinceLemmaGc > d_lemmaGcThreshold
          && (d_params.d_lemmaGcStrategy == LGC_FIXED
              || d_params.d_lemmaGcStrategy == LGC_GEOMETRIC))
      {
        delInactiveLemmas();
      }

      d_ctx.notifyConflictResolved();
    }

    if (resourceLimitsExceeded() && !inconsistent())
    {
      return L_UNDEF;
    }

    if (getCancelFlag())
    {
      return L_UNDEF;
    }

    if (atBaseLevel() && d_params.d_simplifyClauses)
    {
      simplifyClauses();
    }

    if (!decide())
    {
      if (inconsistent())
      {
        return L_FALSE;
      }
      Failure f = OK;
      FinalCheckStatus fcs = d_ctx.finalCheck(f);
      if (f != OK)
      {
        d_lastSearchFailure = f;
      }
      switch (fcs)
      {
        case FC_DONE: return L_TRUE;
        case FC_CONTINUE: break;
        case FC_GIVEUP: return L_UNDEF;
      }
    }

    if (resourceLimitsExceeded() && !inconsistent())
    {
      return L_UNDEF;
    }
  }
}

bool PropCore::canPropagate() const
{
  return d_qhead != d_assignedLiterals.size()
         || d_relevancyPropagator->canPropagate()
         || d_ctx.hasPendingTheoryWork();
}

bool PropCore::propagate()
{
  while (true)
  {
    if (inconsistent())
    {
      return false;
    }
    size_t qhead = d_qhead;
    if (!bcp())
    {
      return false;
    }
    Assert(!inconsistent());
    propagateRelevancy(qhead);
    if (inconsistent())
    {
      return false;
    }
    if (!d_ctx.theoryPropagate())
    {
      return false;
    }
    if (resourceLimitsExceeded())
    {
      d_qhead = qhead;
      return true;
    }
    if (!canPropagate())
    {
      return true;
    }
  }
}

bool PropCore::decide()
{
  BoolVar var;
  bool isPos;
  LBool phase = L_UNDEF;
  d_caseSplitQueue->nextCaseSplit(var, phase);
  if (var == s_nullBoolVar)
  {
    return false;
  }

  isPos = guess(var, phase);

  d_stats.d_numDecisions++;

  pushScope();
  Trace("z3-events") << "DECIDE " << boolVar2Expr(var) << std::endl;
  Trace("z3-events") << "PHASE " << (isPos ? "pos" : "neg") << std::endl;

  Literal l(var, false);
  if (!isPos)
  {
    l.neg();
  }
  assign(l, BJustification::mkAxiom(), true);
  return true;
}

bool PropCore::resolveConflict()
{
  d_stats.d_numConflicts++;
  d_numConflicts++;
  d_numConflictsSinceRestart++;
  d_numConflictsSinceLemmaGc++;
  switch (d_conflict.getKind())
  {
    case BJustification::CLAUSE:
    case BJustification::BIN_CLAUSE: d_stats.d_numSatConflicts++; break;
    default: break;
  }
  if (d_params.d_phaseSelection == PS_THEORY
      || d_params.d_phaseSelection == PS_CACHING_CONSERVATIVE
      || d_params.d_phaseSelection == PS_CACHING_CONSERVATIVE2)
  {
    forgetPhaseOfVarsInCurrentLevel();
  }
  d_ctx.clearPropagationQueues();
  if (!d_conflictResolution->resolve(d_conflict, d_notL))
  {
    return false;
  }

  uint32_t newLvl = d_conflictResolution->getNewScopeLvl();
  size_t numLits = d_conflictResolution->getLemmaNumLiterals();
  Literal* lits = d_conflictResolution->getLemmaLiterals();

  Assert(numLits > 0);
  uint32_t conflictLvl = getAssignLevel(lits[0]);
  Assert(conflictLvl <= d_scopeLvl);

  // When numLits == 1 the default behavior is to go back to the base level.
  // With quantifiers that can be too expensive, since every instance would
  // have to be recreated, so instead the unit is remembered and reasserted
  // after every backtrack, and only one level is popped.
  bool delayForcedRestart =
      d_params.d_delayUnits && numLits == 1 && conflictLvl > d_searchLvl + 1
      && d_unitsToReassert.size() < d_params.d_delayUnitsThreshold;

  if (delayForcedRestart)
  {
    newLvl = conflictLvl - 1;
  }

  // Some of the literals and enodes of the conflict clause are destroyed by
  // backtracking and have to be recreated; cache their generations first.
  if (d_conflictResolution->getLemmaInternLvl() > newLvl)
  {
    cacheGeneration(numLits, lits, newLvl);
  }

  Assert(newLvl < d_scopeLvl);

  // popScopeCore rather than popScope, because the cached generations are
  // still needed to rebuild the literals of the new conflict clause.
  if (relevancy())
  {
    recordRelevancy(numLits, lits);
  }
  size_t numBoolVars = popScopeCore(d_scopeLvl - newLvl);
  Assert(d_scopeLvl == newLvl);
  // The context may still be in conflict after the clauses are reinitialized.
  if (d_conflictResolution->getLemmaInternLvl() > d_scopeLvl)
  {
    std::vector<Node>& atoms = d_conflictResolution->getLemmaAtoms();
    for (size_t i = 0; i < numLits; ++i)
    {
      Literal l = lits[i];
      if (l.var() >= numBoolVars)
      {
        // This variable was deleted during backtracking and must be
        // recreated. Note the atom may be a negative literal: the core
        // creates Boolean variables for not-gates nested inside terms.
        TNode atom = atoms[i];
        d_ctx.internalize(atom, true);
        // getBoolVar would return the null variable for a negated atom, so
        // getLiteral is used instead.
        Literal newL = getLiteral(atom);
        if (l.sign())
        {
          newL.neg();
        }
        lits[i] = newL;
      }
    }
  }
  if (relevancy())
  {
    restoreRelevancy(numLits, lits);
  }
  // The cache is reset manually, since popScopeCore does not do it.
  d_ctx.resetCacheGeneration();

  d_stats.d_numLearnedLits += numLits;
  mkClause(numLits, lits, nullptr, CLS_LEARNED);
  if (delayForcedRestart)
  {
    Assert(numLits == 1);
    Node unit = boolVar2Expr(lits[0].var());
    bool unitSign = lits[0].sign();
    while (unit.getKind() == Kind::NOT)
    {
      unit = unit[0];
      unitSign = !unitSign;
    }
    addUnitToReassert(unit, unitSign, isRelevant(unit));
  }

  d_conflictResolution->releaseLemmaAtoms();
  Trace("z3-events") << "CONFLICT " << numLits << std::endl;
  decayBvarActivity();
  updatePhaseCacheCounter();
  return true;
}

void PropCore::delInactiveLemmas()
{
  if (d_params.d_lemmaGcStrategy == LGC_NONE)
  {
    return;
  }
  if (d_params.d_lemmaGcHalf)
  {
    delInactiveLemmas1();
  }
  else
  {
    delInactiveLemmas2();
  }

  d_numConflictsSinceLemmaGc = 0;
  if (d_params.d_lemmaGcStrategy == LGC_GEOMETRIC)
  {
    d_lemmaGcThreshold = static_cast<uint64_t>(
        static_cast<double>(d_lemmaGcThreshold) * d_params.d_lemmaGcFactor);
  }
}

// ------------------------------------------------- the Boolean structure

void PropCore::assertRoot(TNode n)
{
  d_caseSplitQueue->rootEh(n, false);
  if (isGate(n))
  {
    switch (n.getKind())
    {
      case Kind::AND:
      {
        for (const Node& arg : n)
        {
          d_ctx.internalizeRec(arg, true);
          Literal lit = getLiteral(arg);
          mkRootClause(1, &lit);
        }
        break;
      }
      case Kind::OR:
      {
        LiteralVector lits;
        for (const Node& arg : n)
        {
          d_ctx.internalizeRec(arg, true);
          lits.push_back(getLiteral(arg));
        }
        mkRootClause(lits.size(), lits.data());
        addOrRelWatches(n);
        break;
      }
      case Kind::EQUAL:
      {
        TNode lhs = n[0];
        TNode rhs = n[1];
        d_ctx.internalizeRec(lhs, true);
        d_ctx.internalizeRec(rhs, true);
        Literal l1 = getLiteral(lhs);
        Literal l2 = getLiteral(rhs);
        mkRootClause(l1, ~l2);
        mkRootClause(~l1, l2);
        break;
      }
      case Kind::ITE:
      {
        TNode c = n[0];
        TNode t = n[1];
        TNode e = n[2];
        d_ctx.internalizeRec(c, true);
        d_ctx.internalizeRec(t, true);
        d_ctx.internalizeRec(e, true);
        Literal cl = getLiteral(c);
        Literal tl = getLiteral(t);
        Literal el = getLiteral(e);
        mkRootClause(~cl, tl);
        mkRootClause(cl, el);
        addIteRelWatches(n);
        break;
      }
      default: Unreachable();
    }
    markAsRelevant(n);
  }
  else if (n.getKind() == Kind::DISTINCT)
  {
    assertDistinct(n);
    markAsRelevant(n);
  }
  else
  {
    assertDefault(n);
  }
}

int PropCore::getRandomValue() { return d_ctx.getRandomValue(); }

bool PropCore::isExtDiseqAtom(BoolVar v) { return d_ctx.isExtDiseqAtom(v); }

void PropCore::conflictResolutionEh(BoolVar v)
{
  d_ctx.conflictResolutionEh(v);
}

bool PropCore::assertPermanentLemma(TNode n)
{
  bool local = d_params.d_qiPermanentLocal;
  d_caseSplitQueue->rootEh(n, !local);
  LiteralVector lits;
  if (n.getKind() == Kind::OR)
  {
    for (const Node& arg : n)
    {
      d_ctx.internalizeRec(arg, true);
      lits.push_back(getLiteral(arg));
    }
  }
  else
  {
    d_ctx.internalizeRec(n, true);
    lits.push_back(getLiteral(n));
  }
  if (!local)
  {
    for (Literal l : lits)
    {
      if (l != s_trueLiteral && l != s_falseLiteral)
      {
        markAsRelevant(l);
      }
    }
  }
  bool permanent = lits.size() >= 2;
  Clause* cls = mkClause(lits.size(), lits.data(), nullptr, CLS_TH_LEMMA);
  if (cls != nullptr)
  {
    cls->setPermanent();
  }
  if (local)
  {
    markRootRelevant(n);
  }
  return permanent;
}

void PropCore::reactivatePermanentRoot(TNode n)
{
  d_caseSplitQueue->rootEh(n, false);
  // The atoms of the lemma survive backtracking or are re-internalized with
  // it (reinitClauses); internalizing again only covers the exceptions.
  if (n.getKind() == Kind::OR)
  {
    for (const Node& arg : n)
    {
      d_ctx.internalizeRec(arg, true);
    }
  }
  else
  {
    d_ctx.internalizeRec(n, true);
  }
  markRootRelevant(n);
}

void PropCore::markRootRelevant(TNode n)
{
  if (n.getKind() == Kind::OR)
  {
    addOrRelWatches(n);
    markAsRelevant(n);
    return;
  }
  Literal l = getLiteral(n);
  if (l != s_trueLiteral && l != s_falseLiteral)
  {
    markAsRelevant(l);
  }
}

void PropCore::mkGateConstraints(TNode n)
{
  switch (n.getKind())
  {
    case Kind::NOT: mkNotCnstr(n); break;
    case Kind::AND:
      mkAndCnstr(n);
      addAndRelWatches(n);
      break;
    case Kind::OR:
      mkOrCnstr(n);
      addOrRelWatches(n);
      break;
    case Kind::IMPLIES:
      mkImpliesCnstr(n);
      addImpliesRelWatches(n);
      break;
    case Kind::EQUAL:
      if (n[0].getType().isBoolean())
      {
        mkIffCnstr(n, false);
      }
      break;
    case Kind::ITE:
      mkIteCnstr(n);
      addIteRelWatches(n);
      break;
    case Kind::XOR: mkIffCnstr(n, true); break;
    case Kind::CONST_BOOLEAN: break;
    case Kind::DISTINCT:
      Unreachable() << "z3: formula has not been simplified: " << n;
    default: break;
  }
}

void PropCore::assertDefault(TNode n)
{
  d_ctx.internalize(n, true);
  Literal l = getLiteral(n);
  if (l == s_falseLiteral)
  {
    setConflict(BJustification::mkAxiom());
  }
  else if (l == s_trueLiteral)
  {
    return;
  }
  else
  {
    assign(l, BJustification::mkAxiom());
    markAsRelevant(l);
  }
}

void PropCore::assertDistinct(TNode n)
{
  // Z3 encodes a very large distinct with auxiliary values over a fresh sort.
  // cvc5's rewriter expands distinct during preprocessing, so the core is not
  // expected to meet one at all, let alone a large one; the plain encoding is
  // used in either case.
  assertDefault(n);
}

void PropCore::mkGateClause(size_t numLits, Literal* lits)
{
  mkClause(numLits, lits, nullptr);
}

void PropCore::mkGateClause(Literal l1, Literal l2)
{
  Literal ls[2] = {l1, l2};
  mkGateClause(2, ls);
}

void PropCore::mkGateClause(Literal l1, Literal l2, Literal l3)
{
  Literal ls[3] = {l1, l2, l3};
  mkGateClause(3, ls);
}

void PropCore::mkGateClause(Literal l1, Literal l2, Literal l3, Literal l4)
{
  Literal ls[4] = {l1, l2, l3, l4};
  mkGateClause(4, ls);
}

void PropCore::mkRootClause(size_t numLits, Literal* lits)
{
  mkClause(numLits, lits, nullptr);
}

void PropCore::mkRootClause(Literal l1, Literal l2)
{
  Literal ls[2] = {l1, l2};
  mkRootClause(2, ls);
}

void PropCore::mkRootClause(Literal l1, Literal l2, Literal l3)
{
  Literal ls[3] = {l1, l2, l3};
  mkRootClause(3, ls);
}

void PropCore::addAndRelWatches(TNode n)
{
  if (relevancy())
  {
    RelevancyEh* eh = d_relevancyPropagator->mkAndRelevancyEh(n);
    for (const Node& arg : n)
    {
      // if one child is assigned false, the and-parent must be notified
      addRelWatch(~getLiteral(arg), eh);
    }
  }
}

void PropCore::addOrRelWatches(TNode n)
{
  if (relevancy())
  {
    RelevancyEh* eh = d_relevancyPropagator->mkOrRelevancyEh(n);
    for (const Node& arg : n)
    {
      // if one child is assigned true, the or-parent must be notified
      addRelWatch(getLiteral(arg), eh);
    }
  }
}

void PropCore::addImpliesRelWatches(TNode n)
{
  if (relevancy())
  {
    RelevancyEh* eh = d_relevancyPropagator->mkImpliesRelevancyEh(n);
    addRelWatch(~getLiteral(n[0]), eh);
    addRelWatch(getLiteral(n[1]), eh);
  }
}

void PropCore::addIteRelWatches(TNode n)
{
  if (relevancy())
  {
    RelevancyEh* eh = d_relevancyPropagator->mkIteRelevancyEh(n);
    Literal l = getLiteral(n[0]);
    // when the condition of an ite is assigned, the ite-parent is notified
    addRelWatch(l, eh);
    addRelWatch(~l, eh);
  }
}

void PropCore::mkNotCnstr(TNode n)
{
  Assert(bInternalized(n));
  BoolVar v = getBoolVar(n);
  Literal l(v, false);
  Literal c = getLiteral(n[0]);
  mkGateClause(~l, ~c);
  mkGateClause(l, c);
}

void PropCore::mkAndCnstr(TNode n)
{
  Literal l = getLiteral(n);
  LiteralVector buffer;
  buffer.push_back(l);
  for (const Node& arg : n)
  {
    Literal lArg = getLiteral(arg);
    mkGateClause(~l, lArg);
    buffer.push_back(~lArg);
  }
  mkGateClause(buffer.size(), buffer.data());
}

void PropCore::mkOrCnstr(TNode n)
{
  Literal l = getLiteral(n);
  LiteralVector buffer;
  buffer.push_back(~l);
  for (const Node& arg : n)
  {
    Literal lArg = getLiteral(arg);
    mkGateClause(l, ~lArg);
    buffer.push_back(lArg);
  }
  mkGateClause(buffer.size(), buffer.data());
}

void PropCore::mkImpliesCnstr(TNode n)
{
  Literal l = getLiteral(n);
  LiteralVector buffer;
  buffer.push_back(~l);
  Literal lArg1 = getLiteral(n[0]);
  mkGateClause(l, lArg1);
  buffer.push_back(~lArg1);
  Literal lArg2 = getLiteral(n[1]);
  mkGateClause(l, ~lArg2);
  buffer.push_back(lArg2);
  mkGateClause(buffer.size(), buffer.data());
}

void PropCore::mkIffCnstr(TNode n, bool sign)
{
  if (n.getNumChildren() != 2)
  {
    Unreachable() << "z3: formula has not been simplified: " << n;
  }
  Literal l = getLiteral(n);
  Literal l1 = getLiteral(n[0]);
  Literal l2 = getLiteral(n[1]);
  if (sign)
  {
    l.neg();
  }
  mkGateClause(~l, l1, ~l2);
  mkGateClause(~l, ~l1, l2);
  mkGateClause(l, l1, l2);
  mkGateClause(l, ~l1, ~l2);
}

void PropCore::mkIteCnstr(TNode n)
{
  Literal l = getLiteral(n);
  Literal l1 = getLiteral(n[0]);
  Literal l2 = getLiteral(n[1]);
  Literal l3 = getLiteral(n[2]);
  mkGateClause(~l, ~l1, l2);
  mkGateClause(~l, l1, l3);
  mkGateClause(l, ~l1, ~l2);
  mkGateClause(l, l1, ~l3);
}

// ----------------------------------------------------------------- relevancy

void PropCore::relevantEh(TNode n)
{
  if (bInternalized(n))
  {
    BoolVar v = getBoolVar(n);
    BoolVarData& d = getBdata(v);
    Assert(relevancy());
    // Quantifiers are only asserted when marked relevant; other atoms only
    // when relevancy gates them, and otherwise when they are assigned.
    if (d.isAtom() && (d.isQuantifier() || relevancyGatesAtoms()))
    {
      LBool val = getAssignment(v);
      if (val != L_UNDEF)
      {
        d_ctx.enqueueAtom(Literal(v, val == L_FALSE));
      }
    }
  }
  d_caseSplitQueue->relevantEh(n);
  d_ctx.relevantEh(n);
}

void PropCore::propagateRelevancy(size_t qhead)
{
  if (!relevancy())
  {
    return;
  }
  size_t sz = d_assignedLiterals.size();
  while (qhead < sz)
  {
    Literal l = d_assignedLiterals[qhead];
    Assert(getAssignment(l) == L_TRUE);
    qhead++;
    BoolVar var = l.var();
    TNode n = boolVar2Expr(var);
    d_relevancyPropagator->assignEh(n, !l.sign());
  }
  d_relevancyPropagator->propagate();
}

void PropCore::recordRelevancy(size_t n, const Literal* lits)
{
  // A literal may have been marked relevant inside the scope that conflict
  // resolution pops, in which case it is no longer relevant afterwards. That
  // would make E-matching miss relevant triggers and lose completeness, so
  // the relevancy is recorded here and restored after the pop.
  d_relevantConflictLiterals.clear();
  for (size_t i = 0; i < n; ++i)
  {
    d_relevantConflictLiterals.push_back(isRelevant(lits[i]));
  }
}

void PropCore::restoreRelevancy(size_t n, const Literal* lits)
{
  for (size_t i = 0; i < n; ++i)
  {
    if (d_relevantConflictLiterals[i] && !isRelevant(lits[i]))
    {
      markAsRelevant(lits[i]);
    }
  }
}

// -------------------------------------------------------------------- scopes

void PropCore::pushScope()
{
  d_scopeLvl++;
  d_scopes.push_back(Scope{d_assignedLiterals.size(),
                           d_auxClauses.size(),
                           d_unitsToReassert.size()});
  d_caseSplitQueue->pushScope();
  d_relevancyPropagator->push();
  d_ctx.pushTheoryScope();
}

void PropCore::pushBaseScope()
{
  d_baseScopes.push_back(
      BaseScope{d_lemmas.size(), d_simpQhead, inconsistent()});
  d_baseLvl++;
  // Not really necessary, but it keeps the invariant d_searchLvl >= d_baseLvl.
  d_searchLvl++;
  Assert(d_baseLvl <= d_scopeLvl);
}

size_t PropCore::popScopeCore(size_t numScopes)
{
  Assert(numScopes > 0);
  Assert(numScopes <= d_scopeLvl);
  Assert(d_scopes.size() == d_scopeLvl);

  uint32_t newLvl = d_scopeLvl - static_cast<uint32_t>(numScopes);

  // The order is that of Z3's pop_scope_core, except that the theory side's
  // state other than the trail is popped in one step, after this side's
  // clauses and relevancy: the case split queue, the clauses, relevancy and
  // the quantifier and fingerprint state that the theory side pops are
  // independent of one another.
  cacheGeneration(newLvl);
  d_caseSplitQueue->popScope(numScopes);
  size_t unitsToReassertLim = popClauses(newLvl);
  d_relevancyPropagator->pop(numScopes);
  d_ctx.popTheoryScopeBegin(numScopes);
  unassignToScope(newLvl);
  d_ctx.popTheoryScopeEnd(numScopes, newLvl);
  d_conflictResolution->reset();
  popScopeLevels(newLvl);

  size_t numBoolVars = getNumBoolVars();
  // Any variable at or above numBoolVars was deleted during backtracking.
  reinitClauses(numScopes, numBoolVars);
  reassertUnits(unitsToReassertLim);
  return numBoolVars;
}

void PropCore::popScope(size_t numScopes)
{
  popScopeCore(numScopes);
  d_ctx.resetCacheGeneration();
}

void PropCore::popToBaseLvl()
{
  Assert(d_scopeLvl >= d_baseLvl);
  if (!atBaseLevel())
  {
    popScope(d_scopeLvl - d_baseLvl);
  }
}

void PropCore::popToSearchLvl()
{
  if (d_scopeLvl > d_searchLvl)
  {
    popScope(d_scopeLvl - d_searchLvl);
  }
}

size_t PropCore::popClauses(uint32_t newLvl)
{
  Scope& s = d_scopes[newLvl];
  if (newLvl < d_baseLvl)
  {
    BaseScope& bs = d_baseScopes[newLvl];
    delClauses(d_lemmas, bs.d_lemmasLim);
    d_simpQhead = bs.d_simpQheadLim;
    if (!bs.d_inconsistent)
    {
      d_conflict = s_nullBJustification;
      d_notL = s_nullLiteral;
    }
    d_baseScopes.resize(newLvl);
  }
  else
  {
    d_conflict = s_nullBJustification;
    d_notL = s_nullLiteral;
  }
  delClauses(d_auxClauses, s.d_auxClausesLim);
  return s.d_unitsToReassertLim;
}

void PropCore::unassignToScope(uint32_t newLvl)
{
  unassignVars(d_scopes[newLvl].d_assignedLiteralsLim);
}

void PropCore::popScopeLevels(uint32_t newLvl)
{
  d_scopes.resize(newLvl);
  d_scopeLvl = newLvl;
  if (newLvl < d_baseLvl)
  {
    d_baseLvl = newLvl;
    // not strictly necessary
    d_searchLvl = newLvl;
  }
}

// ----------------------------------------------------------- the Boolean core

void PropCore::setJustification(BoolVar /*v*/,
                                BoolVarData& d,
                                const BJustification& j)
{
  d.setJustification(j);
}

void PropCore::assignCore(Literal l, BJustification j, bool decision)
{
  d_assignedLiterals.push_back(l);
  d_assignment[l.index()] = L_TRUE;
  d_assignment[(~l).index()] = L_FALSE;
  BoolVarData& d = getBdata(l.var());
  setJustification(l.var(), d, j);
  d.d_scopeLvl = d_scopeLvl;
  if (d_params.d_restartAdaptive && d.d_phaseAvailable)
  {
    d_agility *= d_params.d_agilityFactor;
    if (!decision && d.d_phase == l.sign())
    {
      d_agility += (1.0 - d_params.d_agilityFactor);
    }
  }
  bool newPhase = !l.sign();
  d_stats.d_numAssignments++;
  if (d.d_phaseAvailable && d.d_phase != newPhase)
  {
    // reset the birthdate when the phase changes
    d_birthdate[l.var()] = d_stats.d_numAssignments;
  }
  d.d_phaseAvailable = true;
  d.d_phase = newPhase;

  if (d.isAtom()
      && (relevancyLvl() == 0 || (!relevancyGatesAtoms() && !d.isQuantifier())
          || isRelevantCore(l)))
  {
    d_ctx.enqueueAtom(l);
  }

  d_caseSplitQueue->assignLitEh(l);
}

bool PropCore::bcp()
{
  Assert(!inconsistent());
  while (d_qhead < d_assignedLiterals.size())
  {
    if (d_ctx.getCancelFlag())
    {
      return true;
    }
    Literal l = d_assignedLiterals[d_qhead];
    Assert(getAssignment(l) == L_TRUE);
    d_qhead++;
    d_simpCounter--;
    Literal notL = ~l;
    Assert(getAssignment(notL) == L_FALSE);
    WatchList& w = d_watches[l.index()];
    if (binaryClauseOptEnabled())
    {
      // binary clause propagation
      BJustification js(l);
      Literal* it = w.beginLiterals();
      Literal* end = w.endLiterals();
      for (; it != end; ++it)
      {
        Literal l2 = *it;
        switch (getAssignment(l2))
        {
          case L_FALSE:
            d_stats.d_numBinPropagations++;
            setConflict(js, ~l2);
            return false;
          case L_UNDEF:
            d_stats.d_numBinPropagations++;
            assignCore(l2, js);
            break;
          case L_TRUE: break;
        }
      }
    }

    // non-binary clause propagation
    WatchList::ClauseIterator it = w.beginClause();
    WatchList::ClauseIterator it2 = it;
    WatchList::ClauseIterator end = w.endClause();
    for (; it != end; ++it)
    {
      Clause* cls = *it;
      Assert(cls->getLiteral(0) == notL || cls->getLiteral(1) == notL);
      if (cls->getLiteral(0) == notL)
      {
        cls->setLiteral(0, cls->getLiteral(1));
        cls->setLiteral(1, notL);
      }
      Assert(cls->getLiteral(1) == notL);

      Literal firstLit = cls->getLiteral(0);
      LBool firstLitVal = getAssignment(firstLit);

      if (firstLitVal == L_TRUE)
      {
        *it2 = *it;  // the clause is already satisfied, keep it
        it2++;
        continue;
      }
      Literal* it3 = cls->begin() + 2;
      Literal* end3 = cls->end();
      bool foundWatch = false;
      for (; it3 != end3; ++it3)
      {
        if (getAssignment(*it3) != L_FALSE)
        {
          // Swap *it3 with the literal at position 1; the negation of *it3
          // will watch cls from now on.
          d_watches[(~(*it3)).index()].insertClause(cls);
          cls->setLiteral(1, *it3);
          *it3 = notL;
          foundWatch = true;
          break;
        }
      }
      if (foundWatch)
      {
        continue;
      }
      // did not find a watch
      if (firstLitVal == L_FALSE)
      {
        // CONFLICT: copy the remaining watches
        while (it < end)
        {
          *it2 = *it;
          it2++;
          it++;
        }
        Assert(it2 <= end);
        w.setEndClause(it2);
        Assert(isEmptyClause(cls));
        setConflict(BJustification(cls));
        return false;
      }
      // PROPAGATION
      Assert(firstLitVal == L_UNDEF);
      Assert(isUnitClause(cls));
      *it2 = *it;
      it2++;  // keep the clause
      d_stats.d_numPropagations++;
      // It is safe to call assignCore instead of assign, since firstLit is
      // unassigned.
      assignCore(firstLit, BJustification(cls));
      if (d_params.d_relevancyLemma && cls->isLemma())
      {
        markAsRelevant(boolVar2Expr(firstLit.var()));
      }
    }
    Assert(it2 <= end);
    w.setEndClause(it2);
  }
  return true;
}

LBool PropCore::getAssignment(TNode n) const
{
  if (isFalseNode(n))
  {
    return L_FALSE;
  }
  if (n.getKind() == Kind::NOT)
  {
    Assert(bInternalized(n[0]));
    return ~getAssignment(getBoolVarOfId(n[0].getId()));
  }
  Assert(bInternalized(n));
  BoolVar var = getBoolVarOfId(n.getId());
  Assert(var != s_nullBoolVar);
  return getAssignment(var);
}

LBool PropCore::findAssignment(TNode n) const
{
  if (n.getKind() == Kind::NOT)
  {
    TNode arg = n[0];
    if (bInternalized(arg))
    {
      return ~getAssignment(getBoolVarOfId(arg.getId()));
    }
    if (isFalseNode(arg))
    {
      return L_TRUE;
    }
    if (isTrueNode(arg))
    {
      return L_FALSE;
    }
    return L_UNDEF;
  }
  if (bInternalized(n))
  {
    return getAssignment(n);
  }
  if (isFalseNode(n))
  {
    return L_FALSE;
  }
  if (isTrueNode(n))
  {
    return L_TRUE;
  }
  return L_UNDEF;
}

Node PropCore::literal2Expr(Literal l) const
{
  if (l == s_trueLiteral)
  {
    return nodeManager()->mkConst(true);
  }
  if (l == s_falseLiteral)
  {
    return nodeManager()->mkConst(false);
  }
  if (l.sign())
  {
    return nodeManager()->mkNode(Kind::NOT, boolVar2Expr(l.var()));
  }
  return boolVar2Expr(l.var());
}

Literal PropCore::getLiteral(TNode n) const
{
  if (n.getKind() == Kind::NOT)
  {
    return ~getLiteral(n[0]);
  }
  if (isTrueNode(n))
  {
    return s_trueLiteral;
  }
  if (isFalseNode(n))
  {
    return s_falseLiteral;
  }
  Assert(bInternalized(n));
  return Literal(getBoolVar(n), false);
}

void PropCore::setConflict(const BJustification& js, Literal notL)
{
  if (d_conflict == s_nullBJustification)
  {
    d_conflict = js;
    d_notL = notL;
  }
}

void PropCore::rescaleBoolVarActivity()
{
  for (double& a : d_activity)
  {
    a *= s_invActivityLimit;
  }
  d_bvarInc *= s_invActivityLimit;
}

bool PropCore::guess(BoolVar var, LBool phase)
{
  if (isQuantifier(d_boolVar2Expr[var]))
  {
    // Override any decision about how to assign the quantifier: assigning a
    // quantifier to false is the same as making it irrelevant.
    phase = L_FALSE;
  }
  Literal l(var, false);

  if (phase != L_UNDEF)
  {
    return phase == L_TRUE;
  }

  BoolVarData& d = d_bdata[var];
  if (d.tryTrueFirst())
  {
    return true;
  }
  switch (d_params.d_phaseSelection)
  {
    case PS_THEORY:
      if (d_phaseCacheOn && d.d_phaseAvailable)
      {
        return d_bdata[var].d_phase;
      }
      if (!d_phaseCacheOn && d.isTheoryAtom())
      {
        Theory* th = d_ctx.getTheory(d.getTheory());
        LBool thPhase = th->getPhase(var);
        if (thPhase != L_UNDEF)
        {
          return thPhase == L_TRUE;
        }
      }
      if (trackOccs())
      {
        if (d_litOccs[l.index()] == 0)
        {
          return false;
        }
        if (d_litOccs[(~l).index()] == 0)
        {
          return true;
        }
      }
      return d_phaseDefault;
    case PS_CACHING:
    case PS_CACHING_CONSERVATIVE:
    case PS_CACHING_CONSERVATIVE2:
      if (d_phaseCacheOn && d.d_phaseAvailable)
      {
        Trace("z3-events") << "PHASESEL cached " << d_bdata[var].d_phase
                           << std::endl;
        return d_bdata[var].d_phase;
      }
      Trace("z3-events") << "PHASESEL default cacheOn " << d_phaseCacheOn
                         << " available " << d.d_phaseAvailable << std::endl;
      return d_phaseDefault;
    case PS_ALWAYS_FALSE: return false;
    case PS_ALWAYS_TRUE: return true;
    case PS_RANDOM: return d_ctx.getRandomValue() % 2 == 0;
    case PS_OCCURRENCE: return d_litOccs[l.index()] > d_litOccs[(~l).index()];
  }
  Unreachable();
  return false;
}

void PropCore::updatePhaseCacheCounter()
{
  d_phaseCounter++;
  if (d_phaseCacheOn)
  {
    if (d_phaseCounter >= d_params.d_phaseCachingOn)
    {
      d_phaseCounter = 0;
      d_phaseCacheOn = false;
      if (d_params.d_phaseSelection == PS_CACHING_CONSERVATIVE2)
      {
        d_phaseDefault = !d_phaseDefault;
      }
    }
  }
  else
  {
    if (d_phaseCounter >= d_params.d_phaseCachingOff)
    {
      d_phaseCounter = 0;
      d_phaseCacheOn = true;
      if (d_params.d_phaseSelection == PS_CACHING_CONSERVATIVE2)
      {
        d_phaseDefault = !d_phaseDefault;
      }
    }
  }
}

void PropCore::removeWatchLiteral(Clause* cls, size_t idx)
{
  d_watches[(~cls->getLiteral(idx)).index()].removeClause(cls);
}

void PropCore::removeWatch(BoolVar v)
{
  Literal lit(v);
  d_watches[lit.index()].reset();
  d_watches[(~lit).index()].reset();
}

void PropCore::removeClsOccs(Clause* cls)
{
  removeWatchLiteral(cls, 0);
  removeWatchLiteral(cls, 1);
  removeLitOccs(*cls, getNumBoolVars());
}

void PropCore::addLitOccs(const Clause& cls)
{
  if (!trackOccs())
  {
    return;
  }
  for (Literal l : cls)
  {
    incRef(l);
  }
}

void PropCore::removeLitOccs(const Clause& cls, size_t nbv)
{
  if (!trackOccs())
  {
    return;
  }
  for (Literal l : cls)
  {
    if (l.var() < nbv)
    {
      decRef(l);
    }
  }
}

void PropCore::decRef(Literal l)
{
  if (trackOccs() && d_litOccs[l.index()] > 0)
  {
    d_litOccs[l.index()]--;
  }
}

void PropCore::incRef(Literal l)
{
  if (trackOccs())
  {
    d_litOccs[l.index()]++;
  }
}

void PropCore::delClause(Clause* cls)
{
  Assert(d_flushing || !cls->inReinitStack());
  if (!cls->deleted())
  {
    removeClsOccs(cls);
  }
  cls->deallocate();
  d_stats.d_numDelClause++;
}

void PropCore::delClauses(ClauseVector& v, size_t oldSize)
{
  size_t numCollect = v.size() - oldSize;
  if (numCollect == 0)
  {
    return;
  }

  if (numCollect > 1000)
  {
    // For a large batch it is cheaper to mark everything deleted first and
    // then sweep the affected watch lists once.
    UIntSet watches;
    for (size_t i = v.size(); i != oldSize;)
    {
      --i;
      Clause* c = v[i];
      removeLitOccs(*c, getNumBoolVars());
      if (!c->deleted())
      {
        c->markAsDeleted();
      }
      watches.insert((~c->getLiteral(0)).index());
      watches.insert((~c->getLiteral(1)).index());
    }
    for (size_t w = 0, sz = d_watches.size(); w < sz; ++w)
    {
      if (watches.contains(w))
      {
        d_watches[w].removeDeleted();
      }
    }
    for (size_t i = v.size(); i != oldSize;)
    {
      --i;
      v[i]->deallocate();
    }
    d_stats.d_numDelClause += (v.size() - oldSize);
  }
  else
  {
    for (size_t i = v.size(); i != oldSize;)
    {
      --i;
      delClause(v[i]);
    }
  }
  v.resize(oldSize);
}

void PropCore::unassignVars(size_t oldLim)
{
  Assert(oldLim <= d_assignedLiterals.size());

  size_t i = d_assignedLiterals.size();
  while (i != oldLim)
  {
    --i;
    Literal l = d_assignedLiterals[i];
    d_assignment[l.index()] = L_UNDEF;
    d_assignment[(~l).index()] = L_UNDEF;
    BoolVar v = l.var();
    BoolVarData& d = getBdata(v);
    d.setNullJustification();
    d_caseSplitQueue->unassignVarEh(v);
    if (d_hosted && v < d_hostAssigned.size())
    {
      d_hostAssigned[v] = false;
    }
  }

  d_assignedLiterals.resize(oldLim);
  d_qhead = oldLim;
}

bool PropCore::isEmptyClause(const Clause* c) const
{
  size_t numLits = c->getNumLiterals();
  for (size_t i = 0; i < numLits; ++i)
  {
    if (getAssignment(c->getLiteral(i)) != L_FALSE)
    {
      return false;
    }
  }
  return true;
}

bool PropCore::isUnitClause(const Clause* c) const
{
  bool found = false;
  size_t numLits = c->getNumLiterals();
  for (size_t i = 0; i < numLits; ++i)
  {
    switch (getAssignment(c->getLiteral(i)))
    {
      case L_FALSE: break;  // skip
      case L_UNDEF:
        if (found)
        {
          return false;
        }
        found = true;
        break;
      case L_TRUE: return false;  // the clause is already satisfied
    }
  }
  return found;
}

void PropCore::cacheGeneration(uint32_t newScopeLvl)
{
  // When a clause is reinitialized its enodes and literals may have to be
  // recreated. The generation number of a recreated enode must be the one it
  // had before, otherwise it would reset to 0 and defeat the matching-loop
  // heuristics that control quantifier instantiation.
  if (!d_clausesToReinit.empty())
  {
    size_t lim = d_scopeLvl;
    if (d_clausesToReinit.size() <= lim)
    {
      Assert(!d_clausesToReinit.empty());
      lim = d_clausesToReinit.size() - 1;
    }
    for (size_t i = newScopeLvl; i <= lim; ++i)
    {
      for (Clause* cls : d_clausesToReinit[i])
      {
        cacheGeneration(cls, newScopeLvl);
      }
    }
  }
  if (!d_unitsToReassert.empty())
  {
    Scope& s = d_scopes[newScopeLvl];
    for (size_t i = s.d_unitsToReassertLim, sz = d_unitsToReassert.size();
         i < sz;
         ++i)
    {
      d_ctx.cacheGeneration(d_unitsToReassert[i].d_unit, newScopeLvl);
    }
  }
}

void PropCore::cacheGeneration(const Clause* cls, uint32_t newScopeLvl)
{
  cacheGeneration(cls->getNumLiterals(), cls->begin(), newScopeLvl);
}

void PropCore::cacheGeneration(size_t numLits,
                               const Literal* lits,
                               uint32_t newScopeLvl)
{
  for (size_t i = 0; i < numLits; ++i)
  {
    BoolVar v = lits[i].var();
    uint32_t ilvl = getInternLevel(v);
    if (ilvl > newScopeLvl)
    {
      d_ctx.cacheGeneration(boolVar2Expr(v), newScopeLvl);
    }
  }
}

void PropCore::reinitClauses(size_t numScopes, size_t numBoolVars)
{
  // Reinitialize the lemmas that contain Boolean variables deleted during
  // backtracking. A clause has a dead variable if it contains a literal l
  // with l.var() >= numBoolVars.
  if (d_clausesToReinit.empty())
  {
    return;
  }
  size_t lim = d_scopeLvl + numScopes;
  if (d_clausesToReinit.size() <= lim)
  {
    Assert(!d_clausesToReinit.empty());
    lim = d_clausesToReinit.size() - 1;
  }
  for (size_t i = d_scopeLvl + 1; i <= lim; ++i)
  {
    ClauseVector& v = d_clausesToReinit[i];
    for (Clause* cls : v)
    {
      if (cls->deleted())
      {
        cls->releaseAtoms();
        cls->d_reinit = false;
        cls->d_reinternalizeAtoms = false;
        continue;
      }
      Assert(cls->inReinitStack());
      bool keep = false;
      if (cls->reinternalizeAtoms())
      {
        Assert(cls->getNumAtoms() == cls->getNumLiterals());
        for (size_t j = 0; j < 2; ++j)
        {
          Literal l = cls->getLiteral(j);
          if (l.var() < numBoolVars)
          {
            // This variable survived backtracking, so it still watches the
            // clause. Remove the watch, since the clause may end up with
            // different watch literals after reinitialization.
            removeWatchLiteral(cls, j);
          }
        }

        size_t num = cls->getNumLiterals();

        removeLitOccs(*cls, numBoolVars);

        for (size_t j = 0; j < num; ++j)
        {
          TNode atom = cls->getAtom(j);
          bool sign = cls->getAtomSign(j);
          // The atom can be a negation, which happens when the NOT occurs
          // under an uninterpreted function. Reinternalizing a NOT atom
          // requires gateCtx to be false, so that it really is
          // reinternalized.
          bool gateCtx = atom.getKind() != Kind::NOT;
          d_ctx.internalize(atom, gateCtx);
          Assert(bInternalized(atom));
          Literal l(getBoolVar(atom), sign);
          cls->setLiteral(j, l);
          if (cls->getKind() == CLS_TH_LEMMA && !isLocalPermanent(cls))
          {
            markAsRelevant(l);
          }
        }
        int w1Idx = selectWatchLit(cls, 0);
        cls->swapLits(0, w1Idx);
        int w2Idx = selectWatchLit(cls, 1);
        cls->swapLits(1, w2Idx);
        addWatchLiteral(cls, 0);
        addWatchLiteral(cls, 1);

        addLitOccs(*cls);

        Literal l1 = cls->getLiteral(0);
        Literal l2 = cls->getLiteral(1);

        if (getAssignment(l1) == L_FALSE)
        {
          setConflict(BJustification(cls));
        }
        else if (getAssignment(l2) == L_FALSE)
        {
          assign(l1, BJustification(cls));
        }
        keep = true;
      }
      else
      {
        Literal l1 = cls->getLiteral(0);
        Literal l2 = cls->getLiteral(1);
        if (cls->getKind() == CLS_TH_LEMMA && !isLocalPermanent(cls))
        {
          markAsRelevant(l1);
          markAsRelevant(l2);
        }
        if (getAssignment(l1) == L_FALSE && isEmptyClause(cls))
        {
          setConflict(BJustification(cls));
          keep = true;
        }
        else if (getAssignment(l2) == L_FALSE && getAssignment(l1) == L_UNDEF
                 && isUnitClause(cls))
        {
          assign(l1, BJustification(cls));
          keep = true;
        }
      }

      if (keep && d_scopeLvl > d_baseLvl)
      {
        d_clausesToReinit[d_scopeLvl].push_back(cls);
      }
      else
      {
        // The clause no longer needs to be in the reinit stack, because it
        // will be deleted when the base level is backtracked.
        cls->releaseAtoms();
        cls->d_reinit = false;
        cls->d_reinternalizeAtoms = false;
      }
    }
    v.clear();
  }
}

void PropCore::reassertUnits(size_t unitsToReassertLim)
{
  for (size_t i = unitsToReassertLim, sz = d_unitsToReassert.size(); i < sz;
       ++i)
  {
    ReplayUnit& ru = d_unitsToReassert[i];
    d_ctx.internalize(ru.d_unit, true);
    BoolVar v = getBoolVar(ru.d_unit);
    Literal l(v, ru.d_sign);
    assign(l, BJustification::mkAxiom());
    if (ru.d_relevant)
    {
      markAsRelevant(l);
    }
  }
  if (atBaseLevel())
  {
    d_unitsToReassert.clear();
  }
}

bool PropCore::simplifyClause(Clause& cls)
{
  // Simplify the clause using the current assignment, returning true if it is
  // already satisfied. Only safe at the base level, which is also why it is
  // safe for auxiliary clauses: they are deleted on backtracking.
  Assert(d_scopeLvl == d_baseLvl);
  size_t s = cls.getNumLiterals();
  if (getAssignment(cls[0]) == L_TRUE || getAssignment(cls[1]) == L_TRUE)
  {
    return true;
  }

  size_t i = 2;
  size_t j = i;
  bool isTaut = false;
  for (; i < s; ++i)
  {
    Literal l = cls[i];
    switch (getAssignment(l))
    {
      case L_FALSE: decRef(l); break;
      case L_TRUE: isTaut = true; CVC5_FALLTHROUGH;
      case L_UNDEF:
        if (i != j)
        {
          cls.swapLits(i, j);
        }
        j++;
        break;
    }
  }

  if (j < s)
  {
    cls.setNumLiterals(j);
    Assert(j >= 2);
  }

  return isTaut;
}

size_t PropCore::simplifyClauses(ClauseVector& clauses, size_t startingAt)
{
  size_t numDelClauses = 0;
  size_t j = startingAt;
  for (size_t i = startingAt, sz = clauses.size(); i < sz; ++i)
  {
    Clause* cls = clauses[i];
    Assert(!cls->inReinitStack());

    if (cls->deleted())
    {
      delClause(cls);
      numDelClauses++;
    }
    else if (simplifyClause(*cls))
    {
      for (size_t idx = 0; idx < 2; ++idx)
      {
        Literal l0 = (*cls)[idx];
        BJustification l0Js = getJustification(l0.var());
        if (l0Js != s_nullBJustification
            && l0Js.getKind() == BJustification::CLAUSE
            && l0Js.getClause() == cls)
        {
          // cls is the explanation of l0; since we are at the base level it
          // is safe to replace it with an axiom.
          Assert(d_scopeLvl == d_baseLvl);
          d_bdata[l0.var()].setAxiom();
        }
      }
      delClause(cls);
      numDelClauses++;
    }
    else
    {
      clauses[j] = cls;
      ++j;
      d_simpCounter += static_cast<int64_t>(cls->getNumLiterals());
    }
  }
  clauses.resize(j);
  return numDelClauses;
}

void PropCore::simplifyClauses()
{
  // Note that when assumptions are used, d_scopeLvl >= d_searchLvl >
  // d_baseLvl, so no simplification is performed.
  if (d_scopeLvl > d_baseLvl)
  {
    return;
  }

  size_t sz = d_assignedLiterals.size();
  Assert(d_simpQhead <= sz);

  if (d_simpQhead == sz || d_simpCounter > 0)
  {
    return;
  }

  if (d_auxClauses.empty() && d_lemmas.empty())
  {
    return;
  }

  // d_simpCounter balances the cost of simplifyClause: after this runs it
  // approximates the number of literals the next run would have to visit, and
  // it is decremented once per variable visited during propagation.
  d_simpCounter = 0;
  // d_simpQhead detects whether there are new literals assigned at the base
  // level.
  d_simpQhead = d_assignedLiterals.size();

  size_t numDelClauses = 0;

  Assert(d_scopeLvl == d_baseLvl);
  if (d_baseLvl == 0)
  {
    numDelClauses += simplifyClauses(d_auxClauses, 0);
    numDelClauses += simplifyClauses(d_lemmas, 0);
  }
  else
  {
    Scope& s = d_scopes[d_baseLvl - 1];
    BaseScope& bs = d_baseScopes[d_baseLvl - 1];
    numDelClauses += simplifyClauses(d_auxClauses, s.d_auxClausesLim);
    numDelClauses += simplifyClauses(d_lemmas, bs.d_lemmasLim);
  }
  d_stats.d_numDelClauses += numDelClauses;
  d_stats.d_numSimplifications++;
}

namespace {

struct ClauseLt
{
  bool operator()(Clause* cls1, Clause* cls2) const
  {
    return cls1->getActivity() > cls2->getActivity();
  }
};

}  // namespace

void PropCore::delInactiveLemmas1()
{
  // Delete (approximately) half of the low activity lemmas.
  size_t sz = d_lemmas.size();
  size_t startAt = d_baseLvl == 0 ? 0 : d_baseScopes[d_baseLvl - 1].d_lemmasLim;
  Assert(startAt <= sz);
  if (startAt + d_params.d_recentLemmasSize >= sz)
  {
    return;
  }
  size_t endAt = sz - d_params.d_recentLemmasSize;
  Assert(startAt < endAt);
  std::stable_sort(
      d_lemmas.begin() + startAt, d_lemmas.begin() + endAt, ClauseLt());
  size_t startDelAt = (startAt + endAt) / 2;
  size_t i = startDelAt;
  size_t j = i;
  for (; i < endAt; ++i)
  {
    Clause* cls = d_lemmas[i];
    if (canDelete(cls))
    {
      delClause(cls);
    }
    else
    {
      d_lemmas[j] = cls;
      j++;
    }
  }
  // keep the recent clauses
  for (; i < sz; ++i)
  {
    Clause* cls = d_lemmas[i];
    if (cls->deleted() && canDelete(cls))
    {
      delClause(cls);
    }
    else
    {
      d_lemmas[j++] = cls;
    }
  }
  d_lemmas.resize(j);
  if (d_params.d_clauseDecay > 1)
  {
    // rescale the activity
    for (i = startAt; i < j; ++i)
    {
      Clause* cls = d_lemmas[i];
      cls->setActivity(cls->getActivity() / d_params.d_clauseDecay);
    }
  }
}

void PropCore::delInactiveLemmas2()
{
  // A more selective version of delInactiveLemmas1: the lemmas are split into
  // an old and a new group by d_newOldRatio, and a clause is kept based on
  // its activity and its relevancy, with the thresholds depending on which
  // group it is in. A clause with many unassigned literals counts as less
  // relevant.
  size_t sz = d_lemmas.size();
  size_t startAt = d_baseLvl == 0 ? 0 : d_baseScopes[d_baseLvl - 1].d_lemmasLim;
  Assert(startAt <= sz);
  size_t realSz = sz - startAt;
  if (realSz == 0)
  {
    return;
  }
  // the index of the first lemma considered "new"
  size_t newFirstIdx =
      startAt
      + (realSz / d_params.d_newOldRatio) * (d_params.d_newOldRatio - 1);
  Assert(newFirstIdx <= sz);
  size_t i = startAt;
  size_t j = i;
  for (; i < sz; ++i)
  {
    Clause* cls = d_lemmas[i];
    if (canDelete(cls))
    {
      if (cls->deleted())
      {
        delClause(cls);
        continue;
      }
      uint32_t actThreshold =
          d_params.d_oldClauseActivity
          - (d_params.d_oldClauseActivity - d_params.d_newClauseActivity)
                * static_cast<uint32_t>((i - startAt) / realSz);
      if (cls->getActivity() < actThreshold)
      {
        uint32_t relThreshold = (i >= newFirstIdx)
                                    ? d_params.d_newClauseRelevancy
                                    : d_params.d_oldClauseRelevancy;
        if (moreThanKUnassignedLiterals(cls, relThreshold))
        {
          delClause(cls);
          continue;
        }
      }
    }
    d_lemmas[j] = cls;
    j++;
    cls->setActivity(
        static_cast<uint32_t>(cls->getActivity() / d_params.d_invClauseDecay));
  }
  Assert(j <= sz);
  d_lemmas.resize(j);
}

bool PropCore::moreThanKUnassignedLiterals(Clause* cls, size_t k)
{
  Assert(k > 0);
  for (Literal l : *cls)
  {
    if (getAssignment(l) == L_UNDEF)
    {
      k--;
      if (k == 0)
      {
        return true;
      }
    }
  }
  return false;
}

void PropCore::forgetPhaseOfVarsInCurrentLevel()
{
  size_t head =
      d_scopeLvl == 0 ? 0 : d_scopes[d_scopeLvl - 1].d_assignedLiteralsLim;
  size_t sz = d_assignedLiterals.size();
  for (size_t i = head; i < sz; ++i)
  {
    d_bdata[d_assignedLiterals[i].var()].d_phaseAvailable = false;
  }
}

namespace {

/** Undoes setTrueFirstFlag. */
class SetTrueFirstTrail : public Trail
{
 public:
  SetTrueFirstTrail(PropCore& core, BoolVar v) : d_core(core), d_var(v) {}
  void undo() override { d_core.getBdata(d_var).resetTrueFirstFlag(); }

 private:
  PropCore& d_core;
  BoolVar d_var;
};

}  // namespace

void PropCore::setTrueFirstFlag(BoolVar v)
{
  d_ctx.pushTrail(SetTrueFirstTrail(*this, v));
  d_bdata[v].setTrueFirstFlag();
}

BoolVar PropCore::mkBoolVar(TNode n)
{
  Assert(!bInternalized(n));
  size_t id = n.getId();
  BoolVar v = static_cast<BoolVar>(d_bInternalizedStack.size());
  setBoolVar(id, v);
  reservex(d_bdata, v + 1, BoolVarData());
  reservex(d_activity, v + 1, 0.0);
  reservex(d_boolVar2Expr, v + 1, Node::null());
  d_boolVar2Expr[v] = n;
  reservex(d_litScores[0], v + 1, 0.0);
  reservex(d_litScores[1], v + 1, 0.0);
  d_litScores[0][v] = 0.0;
  d_litScores[1][v] = 0.0;
  reservex(d_birthdate, v + 1, static_cast<uint64_t>(0));
  d_birthdate[v] = 0;

  Literal l(v, false);
  Literal notL(v, true);
  size_t aux = std::max(l.index(), notL.index()) + 1;
  reservex(d_assignment, aux, static_cast<int8_t>(L_UNDEF));
  d_assignment[l.index()] = L_UNDEF;
  d_assignment[notL.index()] = L_UNDEF;
  if (d_watches.size() < aux)
  {
    d_watches.resize(aux);
  }
  Assert(d_assignment.size() == d_watches.size());
  d_watches[l.index()].reset();
  d_watches[notL.index()].reset();
  reservex(d_litOccs, aux, static_cast<uint32_t>(0));
  d_litOccs[l.index()] = 0;
  d_litOccs[notL.index()] = 0;
  BoolVarData& data = d_bdata[v];
  // record the level at which the variable was internalized
  data.init(d_scopeLvl);
  if (d_params.d_randomInitialActivity == IA_RANDOM
      || (d_params.d_randomInitialActivity == IA_RANDOM_WHEN_SEARCHING
          && d_ctx.isSearching()))
  {
    d_activity[v] = -((d_ctx.getRandomValue() % 1000) / 1000.0);
  }
  else
  {
    d_activity[v] = 0.0;
  }
  d_caseSplitQueue->mkVarEh(v);
  d_bInternalizedStack.push_back(n);
  d_ctx.pushTrailPtr(&d_mkBoolVarTrail);
  d_stats.d_numMkBoolVar++;
  return v;
}

void PropCore::addScores(size_t n, const Literal* lits)
{
  for (size_t i = 0; i < n; ++i)
  {
    Literal lit = lits[i];
    d_litScores[lit.sign() ? 1 : 0][lit.var()] += 1.0 / n;
  }
}

void PropCore::undoMkBoolVar()
{
  Assert(!d_bInternalizedStack.empty());
  d_stats.d_numDelBoolVar++;
  Node n = d_bInternalizedStack.back();
  size_t nId = n.getId();
  BoolVar v = getBoolVarOfId(nId);
  d_boolVar2Expr[v] = Node::null();
  d_caseSplitQueue->delVarEh(v);
  d_ctx.notifyBoolVarDeleted(n);
  setBoolVar(nId, s_nullBoolVar);
  d_bInternalizedStack.pop_back();
}

bool PropCore::simplifyAuxClauseLiterals(size_t& numLits,
                                         Literal* lits,
                                         LiteralVector& simpLits)
{
  // Simplify the literals of a transient (auxiliary) clause using the current
  // assignment, which is safe because such clauses are deleted on
  // backtracking. Duplicates and false literals are removed; the clause is
  // reported as equivalent to true (by returning false) if it contains a true
  // literal or both l and ~l.
  std::sort(lits, lits + numLits);
  Literal prev = s_nullLiteral;
  size_t j = 0;
  for (size_t i = 0; i < numLits; ++i)
  {
    Literal curr = lits[i];
    switch (getAssignment(curr))
    {
      case L_FALSE:
        if (curr != prev)
        {
          prev = curr;
          simpLits.push_back(~curr);
        }
        break;  // ignore the literal
      case L_UNDEF:
        if (curr == ~prev)
        {
          return false;  // the clause is equivalent to true
        }
        if (curr != prev)
        {
          prev = curr;
          if (i != j)
          {
            lits[j] = lits[i];
          }
          j++;
        }
        break;
      case L_TRUE: return false;  // the clause is equivalent to true
    }
  }
  numLits = j;
  return true;
}

bool PropCore::simplifyAuxLemmaLiterals(size_t& numLits, Literal* lits)
{
  // An auxiliary lemma has the status of a learned clause but was not
  // produced by conflict resolution; a dynamic Ackermann clause is one
  // example. Literals assigned false at the base level are *not* removed,
  // because that would need a justification for the simplification.
  std::sort(lits, lits + numLits);
  Literal prev = s_nullLiteral;
  size_t i = 0;
  size_t j = 0;
  for (; i < numLits; ++i)
  {
    Literal curr = lits[i];
    BoolVar var = curr.var();
    LBool val = L_UNDEF;
    if (getAssignLevel(var) <= d_baseLvl)
    {
      val = getAssignment(curr);
    }
    if (val == L_TRUE)
    {
      return false;  // the clause is equivalent to true
    }
    if (curr == ~prev)
    {
      return false;  // the clause is equivalent to true
    }
    if (curr != prev)
    {
      prev = curr;
      if (i != j)
      {
        lits[j] = lits[i];
      }
      j++;
    }
  }
  numLits = j;
  return true;
}

void PropCore::markForReinit(Clause* cls,
                             uint32_t scopeLvl,
                             bool reinternalizeAtoms)
{
  // A clause may need reinitialization for two reasons. First, it may contain
  // literals created during the search, whose maximum internalization level
  // is scopeLvl; since the clause can outlive that level it has to be rebuilt
  // (reinternalizeAtoms is true in that case). Second, an auxiliary lemma may
  // have been in conflict or propagating when it was created, which has to be
  // rechecked after backtracking.
  Assert(scopeLvl >= d_baseLvl);
  cls->d_reinit = true;
  cls->d_reinternalizeAtoms = reinternalizeAtoms;
  if (scopeLvl >= d_clausesToReinit.size())
  {
    d_clausesToReinit.resize(scopeLvl + 1);
  }
  d_clausesToReinit[scopeLvl].push_back(cls);
}

uint32_t PropCore::getMaxIscopeLvl(size_t numLits, const Literal* lits) const
{
  uint32_t r = 0;
  for (size_t i = 0; i < numLits; ++i)
  {
    uint32_t ilvl = getInternLevel(lits[i].var());
    if (ilvl > r)
    {
      r = ilvl;
    }
  }
  return r;
}

bool PropCore::useBinaryClauseOpt(Literal l1, Literal l2, bool lemma) const
{
  if (!binaryClauseOptEnabled())
  {
    return false;
  }
  // With relevancy enabled, binary clauses must not be used: when a learned
  // clause becomes unit it has to mark the unit literal relevant, and the
  // binary clause encoding cannot distinguish learned from non-learned
  // clauses.
  if (lemma && relevancyLvl() >= 2)
  {
    return false;
  }
  if (d_baseLvl > 0)
  {
    return false;
  }
  if (!lemma && d_scopeLvl > 0)
  {
    return false;
  }
  if (getInternLevel(l1.var()) > 0)
  {
    return false;
  }
  if (getInternLevel(l2.var()) > 0)
  {
    return false;
  }
  return true;
}

int PropCore::selectLearnedWatchLit(const Clause* cls) const
{
  // The learned clauses produced by conflict resolution have the property
  // that the first literal is implied after backtracking, so it is always the
  // first watch. The second watch is the literal with the highest decision
  // level. An unassigned literal was re-created after backtracking, so its
  // level is taken to be the current scope level.
  Assert(cls->getNumLiterals() >= 2);
  int maxFalseIdx = -1;
  uint32_t maxLvl = 0;
  int numLits = static_cast<int>(cls->getNumLiterals());
  for (int i = 1; i < numLits; ++i)
  {
    Literal l = cls->getLiteral(i);
    LBool val = getAssignment(l);
    Assert(val == L_FALSE || val == L_UNDEF);
    uint32_t lvl = val == L_FALSE ? getAssignLevel(l) : d_scopeLvl;
    if (maxFalseIdx == -1 || lvl > maxLvl)
    {
      maxFalseIdx = i;
      maxLvl = lvl;
    }
  }
  return maxFalseIdx;
}

int PropCore::selectWatchLit(const Clause* cls, int startingAt) const
{
  // Pick a watch literal from the positions at or after startingAt:
  //
  //  1. a true literal with the smallest assignment level, which keeps the
  //     clause inactive for as long as possible;
  //  2. otherwise an unassigned literal;
  //  3. otherwise the false literal with the largest assignment level.
  //
  // Rule 3 is what keeps Boolean propagation complete.
  Assert(cls->getNumLiterals() >= 2);
  int minTrueIdx = -1;
  int maxFalseIdx = -1;
  int unknownIdx = -1;
  int n = static_cast<int>(cls->getNumLiterals());
  for (int i = startingAt; i < n; ++i)
  {
    Literal l = cls->getLiteral(i);
    switch (getAssignment(l))
    {
      case L_FALSE:
        if (maxFalseIdx == -1
            || getAssignLevel(l.var())
                   > getAssignLevel(cls->getLiteral(maxFalseIdx).var()))
        {
          maxFalseIdx = i;
        }
        break;
      case L_UNDEF: unknownIdx = i; break;
      case L_TRUE:
        if (minTrueIdx == -1
            || getAssignLevel(l.var())
                   < getAssignLevel(cls->getLiteral(minTrueIdx).var()))
        {
          minTrueIdx = i;
        }
        break;
    }
  }
  if (minTrueIdx != -1)
  {
    return minTrueIdx;
  }
  if (unknownIdx != -1)
  {
    return unknownIdx;
  }
  Assert(maxFalseIdx != -1);
  return maxFalseIdx;
}

void PropCore::addWatchLiteral(Clause* cls, size_t idx)
{
  Assert(idx == 0 || idx == 1);
  Literal l = cls->getLiteral(idx);
  d_watches[(~l).index()].insertClause(cls);
}

Clause* PropCore::mkClause(size_t numLits,
                           Literal* lits,
                           Justification* j,
                           ClauseKind k,
                           ClauseDelEh* delEh)
{
  if (d_hosted && j == nullptr && (k == CLS_TH_AXIOM || k == CLS_TH_LEMMA))
  {
    // A clause of the theory side is a lemma for the host. A clause with a
    // justification stands for its explanation, which reaches the host
    // through the conflicts and propagations it causes instead.
    std::vector<Node> disj;
    for (size_t i = 0; i < numLits; ++i)
    {
      disj.push_back(literal2Expr(lits[i]));
    }
    NodeManager* nm = nodeManager();
    d_hostLemmas.push_back(disj.empty()       ? nm->mkConst(false)
                           : disj.size() == 1 ? disj[0]
                                              : nm->mkNode(Kind::OR, disj));
  }
  LiteralVector simpLits;
  switch (k)
  {
    case CLS_TH_AXIOM:
    case CLS_AUX:
    {
      if (!simplifyAuxClauseLiterals(numLits, lits, simpLits))
      {
        if (j != nullptr && !j->inRegion())
        {
          j->delEh();
          delete j;
        }
        return nullptr;  // the clause is equivalent to true
      }
      if (!simpLits.empty())
      {
        j = d_ctx.mkJustification(UnitResolutionJustification(
            d_ctx, j, simpLits.size(), simpLits.data()));
      }
      break;
    }
    case CLS_TH_LEMMA:
      if (!simplifyAuxLemmaLiterals(numLits, lits))
      {
        if (j != nullptr && !j->inRegion())
        {
          j->delEh();
          delete j;
        }
        return nullptr;  // the clause is equivalent to true
      }
      // simplifyAuxLemmaLiterals does not delete literals assigned to false,
      // so no unit resolution justification is needed.
      break;
    case CLS_LEARNED: addScores(numLits, lits); break;
  }

  uint32_t activity = 1;
  bool lemma = isLemma(k);
  d_stats.d_numMkLits += numLits;

  switch (numLits)
  {
    case 0:
      if (j != nullptr && !j->inRegion())
      {
        d_ctx.addJustification(j);
      }
      setConflict(j == nullptr ? BJustification::mkAxiom() : BJustification(j));
      Assert(inconsistent());
      return nullptr;
    case 1:
    {
      Literal unit = lits[0];
      if (j != nullptr && !j->inRegion())
      {
        d_ctx.addJustification(j);
      }
      assign(unit, j);
      incRef(unit);
      return nullptr;
    }
    case 2:
      if (useBinaryClauseOpt(lits[0], lits[1], lemma))
      {
        Literal l1 = lits[0];
        Literal l2 = lits[1];
        incRef(l1);
        incRef(l2);
        d_watches[(~l1).index()].insertLiteral(l2);
        d_watches[(~l2).index()].insertLiteral(l1);
        if (getAssignment(l1) == L_FALSE)
        {
          assign(l2, BJustification(~l1));
        }
        else if (getAssignment(l2) == L_FALSE)
        {
          assign(l1, BJustification(~l2));
        }
        d_stats.d_numMkBinClause++;
        return nullptr;
      }
      CVC5_FALLTHROUGH;
    default:
    {
      d_stats.d_numMkClause++;
      uint32_t iscopeLvl = lemma ? getMaxIscopeLvl(numLits, lits) : 0;
      Assert(d_scopeLvl >= iscopeLvl);
      bool saveAtoms = lemma && iscopeLvl > d_baseLvl;
      bool reinit = saveAtoms;
      Assert(!lemma || j == nullptr || !j->inRegion());
      Clause* cls =
          Clause::mk(numLits, lits, k, j, delEh, saveAtoms, &d_boolVar2Expr);
      if (lemma)
      {
        cls->setActivity(activity);
        if (k == CLS_LEARNED)
        {
          int w2Idx = selectLearnedWatchLit(cls);
          cls->swapLits(1, w2Idx);
        }
        else
        {
          Assert(k == CLS_TH_LEMMA);
          int w1Idx = selectWatchLit(cls, 0);
          cls->swapLits(0, w1Idx);
          int w2Idx = selectWatchLit(cls, 1);
          cls->swapLits(1, w2Idx);
        }
        d_lemmas.push_back(cls);
        addWatchLiteral(cls, 0);
        addWatchLiteral(cls, 1);
        if (getAssignment(cls->getLiteral(0)) == L_FALSE)
        {
          setConflict(BJustification(cls));
          if (k == CLS_TH_LEMMA && d_scopeLvl > d_baseLvl)
          {
            reinit = true;
            iscopeLvl = d_scopeLvl;
          }
        }
        else if (getAssignment(cls->getLiteral(1)) == L_FALSE)
        {
          assign(cls->getLiteral(0), BJustification(cls));
          if (k == CLS_TH_LEMMA && d_scopeLvl > d_baseLvl)
          {
            reinit = true;
            iscopeLvl = d_scopeLvl;
          }
        }
        if (reinit)
        {
          markForReinit(cls, iscopeLvl, saveAtoms);
        }
      }
      else
      {
        d_auxClauses.push_back(cls);
        addWatchLiteral(cls, 0);
        addWatchLiteral(cls, 1);
        if (getAssignment(cls->getLiteral(0)) == L_FALSE)
        {
          setConflict(BJustification(cls));
        }
        else if (getAssignment(cls->getLiteral(1)) == L_FALSE)
        {
          assign(cls->getLiteral(0), BJustification(cls));
        }
      }

      addLitOccs(*cls);
      return cls;
    }
  }
}

void PropCore::mkClause(Literal l1, Literal l2, Justification* j)
{
  Literal ls[2] = {l1, l2};
  mkClause(2, ls, j);
}

void PropCore::mkClause(Literal l1, Literal l2, Literal l3, Justification* j)
{
  Literal ls[3] = {l1, l2, l3};
  mkClause(3, ls, j);
}

// ------------------------------------------------------------------ host mode

void PropCore::hostInit()
{
  d_hosted = true;
  // cvc5 asserts atoms that are not in this side's encoding of the input,
  // for instance those its rewriter makes of the atoms of lemmas, so their
  // relevance is unknown here. Every assigned atom other than a quantifier
  // reaches the theories, as with --no-z3-relevancy-deliver (B1a, which
  // made no difference); relevancy still restricts matching and the checker.
  d_params.d_relevancyDeliver = false;
  checkPreamble();
  d_ctx.setupContext(d_params.d_autoConfig);
  popToBaseLvl();
  internalizeAssertions();
  d_searchLvl = d_scopeLvl;
  initSearch();
  d_searching = true;
}

void PropCore::hostSyncLevel(uint32_t lvl)
{
  while (d_scopeLvl < lvl)
  {
    pushScope();
  }
  if (d_scopeLvl > lvl)
  {
    popScope(d_scopeLvl - lvl);
  }
}

Literal PropCore::hostLiteral(TNode n)
{
  bool neg = n.getKind() == Kind::NOT;
  TNode atom = neg ? n[0] : n;
  if (!bInternalized(atom))
  {
    d_ctx.internalize(atom, true);
  }
  Literal l = getLiteral(atom);
  return neg ? ~l : l;
}

bool PropCore::hostAssign(Literal l, std::vector<Literal>& conflict)
{
  BoolVar v = l.var();
  if (v >= d_hostAssigned.size())
  {
    d_hostAssigned.resize(v + 1, false);
  }
  switch (getAssignment(l))
  {
    case L_TRUE:
      // This side derived l before the host asserted it, so its own
      // justification stays: the host may have assigned l after literals
      // this side derived from it, which an explanation that stopped at l
      // would then present to the host as reasons for them.
      return true;
    case L_UNDEF: assign(l, BJustification::mkAxiom()); break;
    case L_FALSE:
    {
      // this side derived ~l, which the host contradicts
      conflict.clear();
      conflict.push_back(l);
      std::vector<Literal> todo;
      todo.push_back(~l);
      hostExpand(todo, conflict);
      return false;
    }
  }
  d_hostAssigned[v] = true;
  return true;
}

void PropCore::hostAntecedents(Literal consequent,
                               const BJustification& js,
                               std::vector<Literal>& todo)
{
  switch (js.getKind())
  {
    case BJustification::CLAUSE:
    {
      Clause* cls = js.getClause();
      for (size_t i = 0, n = cls->getNumLiterals(); i < n; ++i)
      {
        Literal l = (*cls)[i];
        if (l != consequent)
        {
          todo.push_back(~l);
        }
      }
      Justification* cjs = cls->getJustification();
      if (cjs != nullptr)
      {
        LiteralVector lits;
        d_ctx.getExplainer().explain(cjs, lits);
        todo.insert(todo.end(), lits.begin(), lits.end());
      }
      break;
    }
    case BJustification::BIN_CLAUSE: todo.push_back(js.getLiteral()); break;
    case BJustification::AXIOM: break;
    case BJustification::JUSTIFICATION:
    {
      LiteralVector lits;
      d_ctx.getExplainer().explain(js.getJustification(), lits);
      todo.insert(todo.end(), lits.begin(), lits.end());
      break;
    }
  }
}

void PropCore::hostExpand(std::vector<Literal>& todo, std::vector<Literal>& out)
{
  std::vector<BoolVar> marked;
  while (!todo.empty())
  {
    Literal a = todo.back();
    todo.pop_back();
    BoolVar v = a.var();
    if (isMarked(v))
    {
      continue;
    }
    setMark(v);
    marked.push_back(v);
    Assert(getAssignment(a) == L_TRUE);
    if (getAssignLevel(v) <= d_baseLvl)
    {
      continue;
    }
    if (isHostAssigned(v))
    {
      out.push_back(a);
      continue;
    }
    hostAntecedents(a, getJustification(v), todo);
  }
  for (BoolVar v : marked)
  {
    unsetMark(v);
  }
  d_ctx.getExplainer().rollback(0);
}

void PropCore::hostExplain(Literal l, std::vector<Literal>& out)
{
  out.clear();
  std::vector<Literal> todo;
  // l itself is expanded even if the host has asserted it since this side
  // propagated it: the host asks because it learned l from this side
  hostAntecedents(l, getJustification(l.var()), todo);
  hostExpand(todo, out);
}

void PropCore::hostExplainConflict(std::vector<Literal>& out)
{
  out.clear();
  Assert(inconsistent());
  std::vector<Literal> todo;
  Literal consequent = s_falseLiteral;
  if (d_notL != s_nullLiteral)
  {
    todo.push_back(d_notL);
    consequent = ~d_notL;
  }
  hostAntecedents(consequent, d_conflict, todo);
  hostExpand(todo, out);
}

void PropCore::hostTakeLemmas(std::vector<Node>& out)
{
  out.insert(out.end(), d_hostLemmas.begin(), d_hostLemmas.end());
  d_hostLemmas.clear();
}

FinalCheckStatus PropCore::hostFinalCheck(Failure& f)
{
  return d_ctx.finalCheck(f);
}

}  // namespace z3
}  // namespace cvc5::internal
