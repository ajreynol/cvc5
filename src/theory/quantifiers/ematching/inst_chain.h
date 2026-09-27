/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Chained instantiation, which matches user triggers against the ground terms
 * of the instantiation lemmas produced by the current round.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INST_CHAIN_H
#define CVC5__THEORY__QUANTIFIERS__INST_CHAIN_H

#include <map>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersState;
class QuantifiersInferenceManager;
class QuantifiersRegistry;
class TermRegistry;

namespace inst {

/**
 * Chained instantiation.
 *
 * E-matching only ever sees ground terms that are in the master equality
 * engine. A term that an instantiation lemma introduces does not get there
 * until the SAT solver has asserted that lemma, so a chain of instantiations
 * in which each link creates the term that fires the next costs one full
 * effort check per link.
 *
 * This class shortens such a chain without moving instantiation earlier in
 * the search. After the ordinary E-matching round has run, it takes the
 * bodies of the instantiation lemmas that round produced, collects the ground
 * terms in them that are not yet in the equality engine, and matches those
 * terms directly against the single user triggers registered here. Matches
 * become instantiations in the same round, and their bodies are mined again,
 * up to a bounded depth. The terms are speculative in that nothing has
 * asserted them yet, but the instantiation lemmas built from them are valid
 * regardless, since an instance of a universally quantified formula holds for
 * any well-sorted ground term.
 *
 * Matching here is deliberately weaker than E-matching: a pattern position
 * that is an instantiation constant binds directly, a ground pattern position
 * must be equal to the corresponding position of the term in the current
 * context, and every other position must agree on its match operator. No
 * search over congruent terms is performed, since the terms being matched do
 * not belong to the equality engine and so have no congruence class to
 * search.
 *
 * Only single user triggers that bind every variable of their quantified
 * formula are indexed. Multi-triggers are left to the ordinary round, since
 * matching one of their patterns against a speculative term says nothing
 * about whether the others match.
 */
class InstChain : protected EnvObj
{
 public:
  InstChain(Env& env,
            QuantifiersState& qs,
            QuantifiersInferenceManager& qim,
            QuantifiersRegistry& qr,
            TermRegistry& tr);
  ~InstChain() {}
  /**
   * Register quantified formula q. This indexes the single user triggers of
   * q by the match operator of their top symbol.
   */
  void registerQuantifier(Node q);
  /** Called once at the beginning of each instantiation round. */
  void resetRound();
  /**
   * Run the chaining pass for the current round. Returns the number of
   * instantiations added.
   */
  uint64_t check();

 private:
  /** A single user trigger of a quantified formula. */
  struct ChainPattern
  {
    /** The quantified formula the pattern belongs to. */
    Node d_quant;
    /** The pattern, in instantiation constant form. */
    Node d_pattern;
  };
  /**
   * Collect the ground terms of body that are candidates for chaining, that
   * is, those that have a match operator this class has a pattern for, that
   * are not already in the equality engine, and that have not been considered
   * yet on this round. Adds them to newTerms.
   */
  void collectNewTerms(TNode body, std::vector<Node>& newTerms);
  /**
   * Match t against each pattern indexed for its match operator, adding an
   * instantiation for each match. Returns the number of instantiations added.
   */
  uint64_t processTerm(TNode t);
  /**
   * Match pattern pat against term t, where subst maps the variable index of
   * each instantiation constant of the pattern's quantified formula to the
   * term it is bound to. Returns true if the match succeeded, in which case
   * the bindings it made have been stored in subst. On failure subst may have
   * been modified, so the caller must discard it.
   */
  bool matchPattern(TNode pat, TNode t, std::vector<Node>& subst) const;
  /** Return true if a and b are known to be equal in the current context. */
  bool areEqualInContext(TNode a, TNode b) const;

  /** Reference to the quantifiers state */
  QuantifiersState& d_qstate;
  /** Reference to the quantifiers inference manager */
  QuantifiersInferenceManager& d_qim;
  /** The quantifiers registry */
  QuantifiersRegistry& d_qreg;
  /** Reference to the term registry */
  TermRegistry& d_treg;
  /** Map from match operator to the patterns whose top symbol has that
   * operator */
  std::map<Node, std::vector<ChainPattern>> d_index;
  /** The quantified formulas that have been registered */
  std::unordered_set<Node> d_registered;
  /** The terms already considered on this round */
  std::unordered_set<Node> d_seen;
  /** Statistics */
  struct Statistics
  {
    Statistics(StatisticsRegistry& sr);
    /** Number of rounds on which chaining considered at least one term */
    IntStat d_rounds;
    /** Number of speculative ground terms considered */
    IntStat d_terms;
    /** Number of (term, pattern) pairs matched */
    IntStat d_pairs;
    /** Number of instantiations added by chaining */
    IntStat d_inst;
  };
  Statistics d_stats;
};

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__INST_CHAIN_H */
