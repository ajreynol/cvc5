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
 * This class is responsible only for matching: it computes the (instantiated)
 * rules whose left-hand side matches a term. Verifying the conditions of a
 * matched rule is the responsibility of the caller, which rewrites them as
 * additional jobs on the rewriter's stack (see theory/rewriter.cpp). Note that
 * conditions are rewritten in the same way as any other term, in particular
 * the rules of this database are applied to them as well. Thus, an :exec rule
 * whose condition requires applying the rule itself does not terminate.
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

  /** An :exec rule that matched a term, instantiated for that term. */
  struct ExecMatch
  {
    /** The identifier of the rule that matched. */
    ProofRewriteRule d_id;
    /** The instantiated conditions of the rule (empty if unconditional). */
    std::vector<Node> d_conds;
    /** The instantiated right-hand side of the rule. */
    Node d_rhs;
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
   * Compute the :exec rules whose left-hand side matches n, and append them,
   * instantiated by the substitution witnessing the match, to matches. The
   * matches are appended in the order in which they should be tried.
   *
   * Note that the conditions of the returned matches are *not* checked here.
   * It is the responsibility of the caller to verify that the conditions of a
   * match rewrite to true before using its right-hand side.
   *
   * @param n The term to match.
   * @param matches The vector to append the matches to.
   */
  void getMatches(const Node& n, std::vector<ExecMatch>& matches) const;

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
