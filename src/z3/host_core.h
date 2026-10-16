/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The ported core under cvc5's propositional engine.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__HOST_CORE_H
#define CVC5__Z3__HOST_CORE_H

#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "context/context.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/incomplete_id.h"
#include "theory/lemma_property.h"
#include "theory/theory.h"
#include "z3/util/literal.h"

namespace cvc5::internal {

class TheoryEngine;

namespace z3 {

class ShadowFeed;
class SharedBackend;

/**
 * Where HostCore sends what it learns: the output channel of the quantifiers
 * theory (Z3QuantifiersEngine).
 */
class HostCoreOutput
{
 public:
  virtual ~HostCoreOutput() = default;
  /**
   * Send a lemma, which must not be preprocessed: its atoms are those of the
   * SAT solver.
   */
  virtual void lemma(const Node& lem, theory::LemmaProperty p) = 0;
  /** Record that a model would be unsound. */
  virtual void setModelUnsound(theory::IncompleteId id) = 0;
};

/**
 * The search contract of cvc5's prop engine (preregistration, facts and
 * checks), implemented over the propositional side of the core in host
 * mode, which mirrors the assignment for the theory side (see
 * PropCore::hostInit). Its scopes follow the SAT context.
 *
 * The core is a shadow of the ground state of cvc5's theories, made from a
 * copy of every fact: it sends instances, conflicts and splits as lemmas,
 * which need no explanation, and reports no propagations, and the formulas
 * it asserts go through cvc5's preprocessing first.
 */
class HostCore : protected EnvObj
{
 public:
  HostCore(Env& env, SharedBackend& backend, HostCoreOutput& out);
  ~HostCore();
  /**
   * Forget the state of the previous context, for the theory engine te; see
   * Z3HostedPropEngine.
   */
  void reset(TheoryEngine* te);

  /** cvc5 registered the atom. */
  void preRegister(TNode atom);
  /** cvc5 asserted the literal. */
  void assertFact(TNode literal);
  /**
   * cvc5 asserted the quantified formula q false, which lem, its
   * skolemization, holds for; see Z3QuantifiersEngine.
   */
  void skolemize(TNode q, TNode lem);
  /** Propagate, and at full effort run the final check. */
  void check(theory::Theory::Effort effort);
  /** Set up the propositional side, once. */
  void presolve();
  /** The feed of the equalities of cvc5's theories. */
  ShadowFeed* getShadowFeed() { return d_feed.get(); }

 private:
  /** Pops the propositional side when the SAT context pops. */
  class PopNotify : public context::ContextNotifyObj
  {
   public:
    PopNotify(context::Context* c, HostCore& hc)
        : context::ContextNotifyObj(c), d_hc(hc)
    {
    }

   protected:
    void contextNotifyPop() override { d_hc.notifyPop(); }

   private:
    HostCore& d_hc;
  };
  /** Note a pop of the SAT context, which syncLevel follows. */
  void notifyPop();
  /** Push or pop the core's scopes to the level of the SAT context. */
  void syncLevel();
  /**
   * Note that the core is in conflict, which it leaves to cvc5's theories to
   * find; see enterConflict in host_core.cpp.
   */
  void enterConflict();
  /** Send the formulas recorded by the propositional side as lemmas. */
  void sendLemmas();
  /**
   * Send the lemma lem, unless it was sent before, or send it again as a
   * lemma local to the SAT context if local is true.
   */
  void sendLemma(const Node& lem, bool local);
  /**
   * The lemma to send for lem. CaDiCaL restarts on a clause that is a unit
   * once the literals false at its base level are removed, to assign that
   * literal at the base level. Most conflicts and many instances are such
   * units here (the conflict that refutes a decision, the instance of an
   * asserted quantifier whose guards are asserted), and the restart undoes
   * every instance made since. Z3's search delays such units instead (its
   * delay_units). Below the second decision level, this
   * weakens such a lemma with the negation of the first decision, so that
   * CaDiCaL assigns its literal out of order at the first decision level
   * and backtracks at most one level (chronological backtracking). The
   * lemma itself is sent at the next check near the base level.
   */
  Node delayUnit(const Node& lem);
  /**
   * Make the relevant, unassigned variables of the core into decisions for
   * cvc5, with a splitting lemma (or v (not v)) that cvc5's decision heuristic
   * must justify, unless one was sent before. These are the gates that
   * relevancy needs assigned, which cvc5 may leave unassigned when it stops
   * on a partial assignment.
   */
  void splitPendingAtoms();
  /**
   * Split on the variables that became relevant since the last call, which
   * cvc5 does not know and are still unassigned, as the core's relevancy
   * queue would decide them.
   */
  void splitNewlyRelevant();
  /** Send the splitting lemma for v, unless it was sent before. */
  void split(BoolVar v);
  /** Propagate, and report what follows; returns false on a conflict. */
  bool propagateAndReport();
  /** The node of the literal l, as cvc5 knows it. */
  Node literalNode(Literal l);
  /**
   * The form of n that cvc5's theories take, by cvc5's lemma preprocessing,
   * adding to defs the definitions of the skolems it introduces; see
   * SmtContext::setCvc5Preprocessor.
   */
  Node preprocessForTheories(TNode n, std::vector<Node>& defs);
  /**
   * The form of n, an atom with closures below it, that cvc5's theories
   * take: its parts outside the closures preprocessed, the closures as they
   * are.
   */
  Node preprocessAroundClosures(TNode n, std::vector<Node>& defs);

  /** The ported core. */
  SharedBackend& d_backend;
  /** The engine, for the prop engine's state. */
  TheoryEngine* d_te;
  /** Where lemmas and propagations go. */
  HostCoreOutput& d_out;
  /** Whether the propositional side was set up (presolve). */
  bool d_setup;
  /** Whether the core is in conflict in the current context. */
  bool d_inConflict;
  /** The level of the SAT context at which the conflict was found. */
  uint32_t d_conflictLevel;
  /** Whether cvc5 must call check again. */
  bool d_needCheck;
  /**
   * The lowest level the SAT context popped to since the last syncLevel, or
   * UINT32_MAX if it did not pop.
   */
  uint32_t d_popLevel;
  /** The atoms registered by cvc5 before the next check. */
  std::vector<Node> d_preregistered;
  /** The lemmas sent, which are permanent in cvc5. */
  std::unordered_set<Node> d_lemmasSent;
  /** The lemmas weakened by delayUnit, to send as they are, see check. */
  std::vector<Node> d_delayedUnits;
  /** The placeholder of each closure, see preprocessAroundClosures. */
  std::unordered_map<Node, Node> d_closureHolders;
  /** Follows the pops of the SAT context. */
  std::unique_ptr<PopNotify> d_popNotify;
  /** See getShadowFeed. */
  std::unique_ptr<ShadowFeed> d_feed;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__HOST_CORE_H */
