/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Executable (interpreted) rewrite trie.
 *
 * This is a lightweight database of rewrite rules that can be applied directly
 * during rewriting, as opposed to the (proof-oriented) RewriteDb. It is
 * populated by the RARE compiler with the subset of rules that are marked with
 * the :exec attribute, and is applied as a small-step "last resort" when the
 * theory rewriter leaves a term unchanged (see theory/rewriter.cpp).
 *
 * The left-hand sides of :exec rules are indexed in an expr::NaryMatchTrie, so
 * that a single candidate term can be tested against all rules at once. The
 * :exec rules are restricted (at compile time) so that any :list variables
 * occur only inside a (f t1 s t2) group with a single non-list needle s; such
 * groups may be nested, e.g. (g (f t1 s t2) r). This keeps matching against the
 * n-ary trie linear in the number of children.
 *
 * This class is responsible only for matching: it computes the rules whose
 * left-hand side matches a term, together with the substitution witnessing the
 * match. Verifying the conditions of a matched rule is the responsibility of
 * the caller, which rewrites them as additional jobs on the rewriter's stack
 * (see theory/rewriter.cpp). Note that conditions are rewritten in the same way
 * as any other term, in particular the rules of this database are applied to
 * them as well. The rewriter breaks the cycle that arises when checking a
 * condition requires checking that same condition again, see
 * Rewriter::d_execCondActive.
 *
 * Matches are instantiated lazily: getCondition and getResult below apply the
 * stored substitution on demand, so that a rule whose first condition fails
 * never pays for instantiating its remaining conditions or its right-hand side.
 */

#include "cvc5_private.h"

#ifndef CVC5__REWRITER__REWRITE_DB_EXEC__H
#define CVC5__REWRITER__REWRITE_DB_EXEC__H

#include <cvc5/cvc5_proof_rule.h>

#include <map>
#include <vector>

#include "expr/nary_match_trie.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace rewriter {

/**
 * The executable rewrite database. Holds all :exec rules and provides a single
 * entry point (getMatches) that computes the rules applicable to a term.
 */
class RewriteDbExec
{
 public:
  /** Information stored for a single :exec rule. */
  struct ExecRule
  {
    /** The identifier of the rule. */
    ProofRewriteRule d_id;
    /** The conditions of the rule (empty if unconditional). */
    std::vector<Node> d_conds;
    /** The right-hand side of the rule. */
    Node d_rhs;
  };

  /**
   * An :exec rule whose left-hand side matched a term, together with the
   * substitution witnessing the match. The conditions and the right-hand side
   * are not instantiated here; use getNumConditions/getCondition/getResult
   * below to instantiate them on demand.
   */
  struct ExecMatch
  {
    /** The identifier of the rule that matched. */
    ProofRewriteRule d_id;
    /**
     * The rule that matched. Note the rules of this database are all added
     * during construction and never removed, hence this pointer remains valid.
     */
    const ExecRule* d_rule;
    /** The variables of the rule that were bound by the match. */
    std::vector<Node> d_vars;
    /** The terms they were bound to. */
    std::vector<Node> d_subs;
  };

  RewriteDbExec(NodeManager* nm);
  ~RewriteDbExec() {}

  /**
   * Add an :exec rule with (possibly empty) conditions conds, left-hand side
   * lhs and right-hand side rhs. This method is called by the auto-generated
   * addRewriteExecRules.
   */
  void addRule(ProofRewriteRule id,
               const std::vector<Node>& conds,
               const Node& lhs,
               const Node& rhs);

  /** Are there no rules in this database? */
  bool empty() const { return d_ruleForLhs.empty(); }

  /**
   * Compute the :exec rules whose left-hand side matches n and append them to
   * matches. The matches are appended in the order the match trie yields them;
   * no priority between rules is defined, and the caller tries them in that
   * order.
   *
   * Note that the conditions of the returned matches are *not* checked here.
   * It is the responsibility of the caller to verify that the conditions of a
   * match rewrite to true before using its right-hand side.
   *
   * @param n The term to match.
   * @param matches The vector to append the matches to.
   */
  void getMatches(const Node& n, std::vector<ExecMatch>& matches) const;

  /** The number of conditions of the rule that m matched. */
  size_t getNumConditions(const ExecMatch& m) const;
  /**
   * Get the i^th condition of the rule that m matched, instantiated by the
   * substitution of m. Returns the null node if the instantiated condition
   * could not be constructed, in which case the match must be abandoned.
   */
  Node getCondition(const ExecMatch& m, size_t i) const;
  /**
   * Get the right-hand side of the rule that m matched, instantiated by the
   * substitution of m. Returns the null node if the instantiated right-hand
   * side could not be constructed, in which case the match must be abandoned.
   */
  Node getResult(const ExecMatch& m) const;

  /** Get the rule information stored for the given left-hand side. */
  const ExecRule& getRuleForLhs(const Node& lhs) const;

 private:
  /** The match trie over the left-hand sides of the :exec rules. */
  expr::NaryMatchTrie d_trie;
  /** Maps each stored left-hand side to its rule id, conditions and rhs. */
  std::map<Node, ExecRule> d_ruleForLhs;
};

}  // namespace rewriter
}  // namespace cvc5::internal

#endif /* CVC5__REWRITER__REWRITE_DB_EXEC__H */
