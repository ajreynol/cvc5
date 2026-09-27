/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Eager instantiation from falsified predicate literals.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INST_STRATEGY_EAGER_LITERAL_H
#define CVC5__THEORY__QUANTIFIERS__INST_STRATEGY_EAGER_LITERAL_H

#include <map>
#include <memory>
#include <vector>

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "util/statistics_stats.h"

namespace cvc5::internal::theory::quantifiers {

class QuantifiersInferenceManager;
class QuantifiersState;

/**
 * An optional, incomplete companion to ordinary instantiation. For a clausal
 * quantifier, a flat predicate literal containing every variable can serve as
 * an anchor. An asserted fact of the opposite polarity determines a complete
 * substitution syntactically, without an equality search or a multi-pattern
 * join. We send its instance only if the rewritten body is false or unit under
 * the SAT assignment. A unit must use only non-Boolean terms that already
 * occur in the triggering fact, to avoid eager term-generation chains.
 *
 * Facts, active quantifiers and anchor cursors follow the SAT context. Rules
 * are immutable and may outlive their assertion. The cumulative candidate
 * budget is reset at presolve, and is not refunded by backtracking. Exhausting
 * it, or skipping an unsupported formula, leaves ordinary instantiation alone.
 */
class InstStrategyEagerLiteral : protected EnvObj
{
 public:
  InstStrategyEagerLiteral(Env& env,
                           QuantifiersState& qs,
                           QuantifiersInferenceManager& qim);
  /** Reset the cumulative work budget for a new check-sat. */
  void presolve();
  /** Register an eligible, unowned or E-matching-owned quantifier. */
  void registerQuantifier(Node q);
  /** Activate a positively asserted quantifier. */
  void assertQuantifier(Node q);
  /** Record a SAT assertion. No instantiation occurs in this callback. */
  void notifyAssertedFact(TNode fact);
  /** Process candidates at standard effort, stopping after one new lemma. */
  void check();

 private:
  using FactKey = std::pair<Node, bool>;
  struct FactList
  {
    explicit FactList(context::Context* c) : d_list(c) {}
    context::CDList<Node> d_list;
  };
  struct Anchor
  {
    Anchor(context::Context* c, Node q, Node atom, FactList& facts);
    Node d_quant;
    Node d_atom;
    /** Variable index for each argument, or -1 for an exact ground argument. */
    std::vector<int64_t> d_varIndices;
    FactList& d_facts;
    context::CDO<size_t> d_index;
  };
  FactList& getFacts(const FactKey& key);
  /** Return -1 for rejected, 0 for conflicting, 1 for unit. */
  int classify(Node body, Node fact);

  QuantifiersState& d_qstate;
  QuantifiersInferenceManager& d_qim;
  std::map<FactKey, std::unique_ptr<FactList>> d_facts;
  std::vector<std::unique_ptr<Anchor>> d_anchors;
  context::CDHashSet<Node> d_active;
  context::CDHashSet<Node> d_seenFacts;
  uint64_t d_candidates;
  IntStat d_statCandidates;
  IntStat d_statConflicts;
  IntStat d_statUnits;
  IntStat d_statRejected;
};

}  // namespace cvc5::internal::theory::quantifiers

#endif
