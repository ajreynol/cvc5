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
 */

#include "cvc5_private.h"

#ifndef CVC5__REWRITER__REWRITE_DB_EXEC__H
#define CVC5__REWRITER__REWRITE_DB_EXEC__H

#include <cvc5/cvc5_proof_rule.h>

#include <map>

#include "expr/nary_match_trie.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace rewriter {

/**
 * The executable rewrite database. Holds all :exec rules and provides a single
 * small-step entry point (rewrite) that attempts to apply one of them.
 */
class RewriteDbExec
{
 public:
  /** Information stored for a single :exec rule. */
  struct ExecRule
  {
    /** The identifier of the rule. */
    ProofRewriteRule d_id;
    /** The right-hand side of the rule. */
    Node d_rhs;
  };

  RewriteDbExec(NodeManager* nm);
  ~RewriteDbExec() {}

  /**
   * Add an :exec rule with left-hand side lhs and right-hand side rhs. This
   * method is called by the auto-generated addRewriteExecRules.
   */
  void addRule(ProofRewriteRule id, const Node& lhs, const Node& rhs);

  /** Are there no rules in this database? */
  bool empty() const { return d_ruleForLhs.empty(); }

  /**
   * Try to rewrite n with a single :exec rule (a small step). If some rule's
   * left-hand side matches n, returns the instantiated right-hand side and sets
   * id to the identifier of the rule that was used (so that proof generation
   * can be linked to it). Otherwise returns the null node and leaves id
   * unchanged.
   */
  Node rewrite(const Node& n, ProofRewriteRule& id);

  /** Get the rule information stored for the given left-hand side. */
  const ExecRule& getRuleForLhs(const Node& lhs) const;

 private:
  /** Pointer to the node manager. */
  NodeManager* d_nm;
  /** The match trie over the left-hand sides of the :exec rules. */
  expr::NaryMatchTrie d_trie;
  /** Maps each stored left-hand side to its rule id and right-hand side. */
  std::map<Node, ExecRule> d_ruleForLhs;
};

}  // namespace rewriter
}  // namespace cvc5::internal

#endif /* CVC5__REWRITER__REWRITE_DB_EXEC__H */
