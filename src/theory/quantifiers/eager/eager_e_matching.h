/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The quantifiers module of the eager E-matching core.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__EAGER_E_MATCHING_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__EAGER_E_MATCHING_H

#include <memory>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "context/context.h"
#include "theory/incomplete_id.h"
#include "theory/inference_id.h"
#include "theory/lemma_property.h"
#include "theory/quantifiers/eager/relevancy_tracker.h"
#include "theory/quantifiers/eager/smt_context.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

class LemmaProofGenerator;

/**
 * The module of cvc5's quantifiers engine with --eager-e-matching, which owns
 * the ported core (SmtContext) and is its boundary with cvc5: it follows the
 * SAT context, gives the core cvc5's facts and checks, and sends cvc5 the
 * core's lemmas, with their proofs. cvc5's own theories do the ground
 * reasoning, with their equality engines and theory combination; the core
 * matches and instantiates over a shadow of the ground state:
 * - it receives every literal the SAT solver asserts, for its E-graph and
 *   for relevancy (RelevancyTracker), and the equalities cvc5's theories
 *   derive, through the master equality engine, of whose merges the
 *   quantifiers engine notifies this module (notifyMasterMerge);
 * - the formulas it asserts go through cvc5's preprocessing first.
 *
 * The rest is the quantifiers engine's: it registers the quantified formulas,
 * and skolemizes those asserted false. The core also takes the skolemization
 * of a quantified formula assigned false that is relevant to it, so that the
 * witnesses are relevant as well.
 *
 * Soundness. What this module gives cvc5 is limited to the following, so
 * that no error in the core (its E-graph, relevancy, matching, or how it
 * follows the SAT and user contexts) can make cvc5 answer wrongly; at most
 * it makes the core miss instances or search worse.
 * - Lemmas, each valid on its own, interpreting each skolem as the term it
 *   stands for (cvc5's skolems are canonical), whatever is asserted, so
 *   also after the user pop of the scope it was made in:
 *   - an instance of a quantified formula q of cvc5, (=> q q[1]{x->t}),
 *     made by LemmaProofGenerator::mkInstance, which checks that the terms
 *     t are closed and of the types of the variables x;
 *   - the skolemization of q, made by cvc5's Skolemize;
 *   - the definition of a skolem, made by cvc5's preprocessing of one of
 *     these lemmas;
 *   - one of these, or its preprocessed form, weakened by the negation of a
 *     decision (delayUnit).
 *   With proofs, each has a proof (LemmaProofGenerator), which shows it.
 * - Nothing else: no conflicts (an inconsistency of the core is left for
 *   cvc5's theories to find, see enterConflict), no propagations, no
 *   explanations, and no decisions.
 * - No claim of completeness (checkCompleteFor), so a model is never
 *   accepted because of the core, and none while the core is inconsistent
 *   (checkCore marks the model unsound then).
 */
class EagerEMatching : public theory::quantifiers::QuantifiersModule
{
 public:
  EagerEMatching(Env& env,
                 theory::quantifiers::QuantifiersState& qs,
                 theory::quantifiers::QuantifiersInferenceManager& qim,
                 theory::quantifiers::QuantifiersRegistry& qr,
                 theory::quantifiers::TermRegistry& tr);
  ~EagerEMatching();
  /** Make the core, for the theory engine te. */
  void finishInit(TheoryEngine* te) override;
  void presolve() override;
  /** Assert the preprocessed assertions to the core. */
  void ppNotifyAssertions(const std::vector<Node>& assertions) override;
  /** Run the core, at standard and full effort. */
  bool needsCheck(theory::Theory::Effort e) override;
  void check(theory::Theory::Effort e, QEffort quant_e) override;
  void preRegisterQuantifier(Node q) override;
  /**
   * The core claims completeness for no quantified formula: whether a model
   * satisfies them is for the other modules of the quantifiers engine.
   */
  bool checkCompleteFor(CVC5_UNUSED Node q) override { return false; }
  /** Give the merge to the core. */
  void notifyMasterMerge(TNode t1, TNode t2) override;
  std::string identify() const override { return "EagerEMatching"; }

  // ------------------------------------------------ called by the core
  /** cvc5 asserted the literal; see RelevancyTracker. */
  void assertFact(TNode literal);
  /**
   * Send the lemma lem, unless it was sent before, or send it again as a
   * lemma local to the SAT context if local is true.
   */
  void sendLemma(const Node& lem, bool local);
  /**
   * The instance of the core's quantified formula q for terms, in the form
   * cvc5's theories take, see internalizeInstance. The lemma sent
   * for it is cvc5's instantiation lemma, proven by d_pg.
   */
  Node mkInstance(TNode q,
                  const std::vector<Node>& terms,
                  std::vector<Node>& defs);
  /**
   * The skolemization of the core's quantified formula q, in the form cvc5's
   * theories take, see skolemize. The lemma sent for it is
   * the one of cvc5's quantifiers engine, with its proof.
   */
  Node mkSkolemization(TNode q, std::vector<Node>& defs);

 private:
  /** cvc5 registered the atom. */
  void preRegister(TNode atom);
  /**
   * Give the core the literals asserted since the last check, then
   * propagate, and at full effort run the final check.
   */
  void checkCore(theory::Theory::Effort effort);
  /** Pops the propositional side when the SAT context pops. */
  class PopNotify : public context::ContextNotifyObj
  {
   public:
    PopNotify(context::Context* c, EagerEMatching& hc)
        : context::ContextNotifyObj(c), d_hc(hc)
    {
    }

   protected:
    void contextNotifyPop() override { d_hc.notifyPop(); }

   private:
    EagerEMatching& d_hc;
  };
  /**
   * Send a lemma, which must not be preprocessed: its atoms are those of the
   * SAT solver.
   */
  void lemma(const Node& lem, theory::LemmaProperty p);
  /** Note a pop of the SAT context, which syncLevel follows. */
  void notifyPop();
  /**
   * Push or pop the core's scopes to the level of the SAT context: the
   * core's scope level is the SAT context's level minus one, so that its
   * level 0 is the SAT context's level 1, below every user scope.
   */
  void syncLevel();
  /**
   * Note that the core is in conflict, which it leaves to cvc5's theories to
   * find; see enterConflict in eager_e_matching.cpp.
   */
  void enterConflict();
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
  /** Propagate; returns false on a conflict, which it enters. */
  bool propagateAndReport();
  /**
   * The core's form of n, a formula of cvc5: its quantified formulas over
   * the canonical variables the core expects (see
   * theory/quantifiers/eager/quantifier_normalizer.h). The atoms of n that
   * change are recorded, for toHost.
   */
  Node toCore(TNode n);
  /** Record the atoms of n that its core's form nc renames, for toHost. */
  void recordRenamedAtoms(TNode n, TNode nc);
  /**
   * cvc5's form of n, a formula of the core: the atoms the core renamed are
   * cvc5's again. The other atoms, the new quantified formulas of the
   * instances for example, are the same for both. Since alpha-equivalent
   * atoms of cvc5 have the same core's form, this is one of them.
   */
  Node toHost(TNode n);
  /**
   * cvc5's form of the lemma norm the core sends: the form it was made from,
   * which has a proof, when proofs are produced, and toHost otherwise.
   */
  Node toHostLemma(TNode norm);
  /**
   * The core's form of n, a lemma of cvc5, in the form cvc5's theories
   * take, by cvc5's lemma preprocessing, adding to defs the definitions of
   * the skolems it introduces, and setting pp to the rewrite of n by the
   * preprocessing.
   */
  Node preprocessForTheories(TNode n,
                             std::vector<Node>& defs,
                             TrustNode& pp,
                             theory::InferenceId id);
  /**
   * The lemma of cvc5's Skolemize utility that skolemizes q, which the
   * quantifiers engine sent when q was asserted false.
   */
  TrustNode getSkolemization(TNode q);
  /**
   * Preprocess the lemma trn proves, which the core sends, into the form
   * cvc5's theories take, as mkInstance and mkSkolemization do.
   */
  Node preprocessLemma(const TrustNode& trn,
                       std::vector<Node>& defs,
                       theory::InferenceId id);

  /** The engine, for the prop engine's state. */
  TheoryEngine* d_te;
  /** Whether the propositional side was set up (presolve). */
  bool d_setup;
  /**
   * Whether the SAT context popped to level 0, which reset-assertions does:
   * the core is then made again, at the next syncLevel.
   */
  bool d_reset;
  /**
   * The level of the SAT context below the first decision of the current
   * search: that of presolve, plus a decision level for the activation
   * literal of each of cvc5's user scopes.
   */
  uint32_t d_searchBaseLevel;
  /**
   * Whether the core is in conflict in the current context. The conflict
   * holds until the SAT context pops below the level it was found at.
   */
  context::CDO<bool> d_inConflict;
  /** Whether cvc5 must call check again. */
  bool d_needCheck;
  /**
   * The lowest level the SAT context popped to since the last syncLevel, or
   * UINT32_MAX if it did not pop.
   */
  uint32_t d_popLevel;
  /**
   * The atoms registered by cvc5, to take before the next check from
   * d_preregisteredHead on. The state below that refers to cvc5's atoms and
   * lemmas is in the user context, so that none of a popped user scope is
   * used after the pop.
   */
  context::CDList<Node> d_preregistered;
  context::CDO<size_t> d_preregisteredHead;
  /**
   * The lemmas sent. cvc5 keeps a lemma until the pop of the user scope of
   * its atoms, so this is in the user context.
   */
  context::CDHashSet<Node> d_lemmasSent;
  /**
   * The lemmas weakened by delayUnit, to send as they are from
   * d_delayedUnitsHead on, see checkCore.
   */
  context::CDList<Node> d_delayedUnits;
  context::CDO<size_t> d_delayedUnitsHead;
  /**
   * For each atom of cvc5 that toCore renamed, the core's form and cvc5's,
   * the first one renamed to it in the current user scopes: alpha-equivalent
   * atoms of cvc5 have the same core's form.
   */
  context::CDHashMap<Node, Node> d_hostAtom;
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
  /** Follows the pops of the SAT context. */
  std::unique_ptr<PopNotify> d_popNotify;
  /** Gives the core the literals the SAT solver asserts. */
  std::unique_ptr<RelevancyTracker> d_tracker;
  /** The ported core, under cvc5's prop engine. */
  std::unique_ptr<SmtContext> d_core;
};

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER__EAGER_E_MATCHING_H */
