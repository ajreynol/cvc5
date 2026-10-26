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

#ifndef CVC5__Z3__QUANTIFIERS__HOST_CORE_H
#define CVC5__Z3__QUANTIFIERS__HOST_CORE_H

#include <functional>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "context/context.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/decision_strategy.h"
#include "theory/incomplete_id.h"
#include "theory/inference_id.h"
#include "theory/lemma_property.h"
#include "theory/theory.h"
#include "z3/util/literal.h"

namespace cvc5::internal {

class TheoryEngine;

namespace theory::quantifiers {
class QuantifiersInferenceManager;
}

namespace z3 {

class ShadowFeed;
class LemmaProofGenerator;
class PropCore;
class SmtContext;

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
  /**
   * The lemma of cvc5's quantifiers engine that skolemizes the quantified
   * formula q, in cvc5's form, which the core takes when q is assigned false
   * and relevant.
   */
  using Skolemizer = std::function<TrustNode(TNode)>;
  /**
   * Lemmas go through qim, the inference manager of the quantifiers theory,
   * and skolemizations come from skolemizer.
   */
  HostCore(Env& env,
           theory::quantifiers::QuantifiersInferenceManager& qim,
           Skolemizer skolemizer);
  ~HostCore();
  /**
   * Make a fresh core and forget the state of the previous one, for the
   * theory engine te.
   */
  void reset(TheoryEngine* te);
  /** The theory side of the core. Requires that reset has been called. */
  SmtContext& getContext();
  /** The propositional side of the core. Requires that reset has been called.
   */
  PropCore& getPropCore();

  /**
   * Assert the input formulas, cvc5's preprocessed assertions, to the core,
   * before cvc5 converts them.
   */
  void assertInput(const std::vector<Node>& assertions);
  /** cvc5 registered the atom. */
  void preRegister(TNode atom);
  /** cvc5 asserted the literal. */
  void assertFact(TNode literal);
  /** Propagate, and at full effort run the final check. */
  void check(theory::Theory::Effort effort);
  /** Set up the propositional side, once. */
  void presolve();
  /** The feed of the equalities of cvc5's theories. */
  ShadowFeed* getShadowFeed() { return d_feed.get(); }

 private:
  /**
   * The decisions the core asks cvc5 for: each atom it splits on, whenever
   * it is unassigned. cvc5 asks its decision strategies before it decides
   * on its own.
   */
  class SplitStrategy : public theory::DecisionStrategy
  {
   public:
    SplitStrategy(Env& env, TheoryEngine*& te)
        : theory::DecisionStrategy(env), d_te(te)
    {
    }
    void initialize() override {}
    Node getNextDecisionRequest() override;
    std::string identify() const override { return "z3-split"; }
    /** Ask for a decision on the atom a. */
    void add(const Node& a) { d_atoms.push_back(a); }
    void clear() { d_atoms.clear(); }

   private:
    /** The engine of the core, for its prop engine. */
    TheoryEngine*& d_te;
    /** The atoms to decide. */
    std::vector<Node> d_atoms;
  };
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
  /**
   * Send a lemma, which must not be preprocessed: its atoms are those of the
   * SAT solver.
   */
  void lemma(const Node& lem, theory::LemmaProperty p);
  /** Note a pop of the SAT context, which syncLevel follows. */
  void notifyPop();
  /** Push or pop the core's scopes to the level of the SAT context. */
  void syncLevel();
  /**
   * Note that the core is in conflict, which it leaves to cvc5's theories to
   * find; see enterConflict in host_core.cpp.
   */
  void enterConflict();
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
   * cvc5 (see SplitStrategy). These are the gates that relevancy needs
   * assigned, which cvc5 may leave unassigned when it stops on a partial
   * assignment.
   */
  void splitPendingAtoms();
  /**
   * Split on the variables that became relevant since the last call, which
   * cvc5 does not know and are still unassigned, as the core's relevancy
   * queue would decide them.
   */
  void splitNewlyRelevant();
  /** Have cvc5 decide v, unless it was asked before. */
  void split(BoolVar v);
  /** Propagate, and report what follows; returns false on a conflict. */
  bool propagateAndReport();
  /**
   * The core's form of n, a formula of cvc5: its quantified formulas over
   * the canonical variables the core expects (see z3/util/ast.h). The atoms
   * of n that change are recorded, for toHost.
   */
  Node toCore(TNode n);
  /** Record the atoms of n that its core's form nc renames, for toHost. */
  void recordRenamedAtoms(TNode n, TNode nc);
  /**
   * cvc5's form of n, a formula of the core: the atoms the core renamed are
   * cvc5's again. The other atoms, the new quantified formulas of the
   * instances for example, are the same for both.
   */
  Node toHost(TNode n);
  /**
   * The core's form of n, a formula of cvc5, in the form cvc5's theories
   * take, by cvc5's lemma preprocessing, adding to defs the definitions of
   * the skolems it introduces, and setting pp to the rewrite of n by the
   * preprocessing.
   */
  Node preprocessForTheories(TNode n,
                             std::vector<Node>& defs,
                             TrustNode& pp,
                             theory::InferenceId id);
  /**
   * The instance of the core's quantified formula q for terms, in the form
   * cvc5's theories take, see SmtContext::setInstanceMaker. The lemma sent
   * for it is cvc5's instantiation lemma, proven by d_pg.
   */
  Node mkInstance(TNode q,
                  const std::vector<Node>& terms,
                  std::vector<Node>& defs);
  /**
   * The skolemization of the core's quantified formula q, in the form cvc5's
   * theories take, see SmtContext::setSkolemizer. The lemma sent for it is
   * the one of cvc5's quantifiers engine, with its proof.
   */
  Node mkSkolemization(TNode q, std::vector<Node>& defs);
  /**
   * Preprocess the lemma trn proves, which the core sends, into the form
   * cvc5's theories take, as mkInstance and mkSkolemization do.
   */
  Node preprocessLemma(const TrustNode& trn,
                       std::vector<Node>& defs,
                       theory::InferenceId id);

  /** The ported core. */
  std::unique_ptr<SmtContext> d_ctx;
  /** The engine, for the prop engine's state. */
  TheoryEngine* d_te;
  /** Where lemmas go. */
  theory::quantifiers::QuantifiersInferenceManager& d_qim;
  /** See Skolemizer. */
  Skolemizer d_skolemizer;
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
  /**
   * For each atom of cvc5 that toCore renamed, the core's form and cvc5's.
   * Alpha-equivalent atoms of cvc5 would have the same core's form, which
   * does not happen with the inputs the core takes: the core's forms keep
   * the quantifier names (qid) and patterns.
   */
  std::unordered_map<Node, Node> d_hostAtom;
  /** The atoms split on, see split. */
  std::unordered_set<Node> d_splitAtoms;
  /**
   * Proves the lemmas the core sends, and gives, for an instance or the
   * definition of a skolem, the lemma cvc5 is sent for it.
   */
  std::unique_ptr<LemmaProofGenerator> d_pg;
  /**
   * The inference of each lemma the core sends, in cvc5's form: an instance,
   * a skolemization, or the definition of a skolem in one of these, which
   * has the inference of that lemma. A weakened lemma has the inference of
   * the lemma it weakens.
   */
  std::unordered_map<Node, theory::InferenceId> d_lemmaIds;
  /** See SplitStrategy. */
  std::unique_ptr<SplitStrategy> d_splitStrategy;
  /** Follows the pops of the SAT context. */
  std::unique_ptr<PopNotify> d_popNotify;
  /** See getShadowFeed. */
  std::unique_ptr<ShadowFeed> d_feed;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIERS__HOST_CORE_H */
