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
 * the :exec attribute.
 *
 * :exec rules come in two forms:
 * - Rules with no list variables have an arbitrary application left-hand side
 *   and are matched directly against a candidate subterm (like an ordinary
 *   first-order rewrite).
 * - Rules that use list variables are restricted to the pattern
 *     (f t1 s t2)
 *   where f is an n-ary operator, t1 and t2 are (distinct) list variables and
 *   s is a single non-list "needle". Since the needle contains no list
 *   variables, a candidate term (f a0 ... a_{m-1}) is matched by trying each
 *   child a_i as the needle (binding t1 to the prefix and t2 to the suffix).
 *
 * Both forms are indexed in discrimination tries so that a single subterm can
 * be tested against all rules at once: direct patterns share one trie, while
 * needles are indexed in a per-operator-kind trie.
 */

#include "cvc5_private.h"

#ifndef CVC5__REWRITER__REWRITE_DB_EXEC__H
#define CVC5__REWRITER__REWRITE_DB_EXEC__H

#include <cvc5/cvc5_proof_rule.h>

#include <map>
#include <vector>

#include "expr/node.h"

namespace cvc5::internal {
namespace rewriter {

/**
 * A discrimination trie (a.k.a. match trie) over needle patterns. Terms are
 * indexed by a pre-order traversal of their structure, where each application
 * is indexed by its operator and arity, and each free variable introduces a
 * variable branch. Each stored needle is associated with an integer datum (an
 * index into the owning RewriteDbExec's rule table).
 *
 * This mirrors expr::MatchTrie, specialized to store rule indices at its
 * terminals and to return the first match together with its substitution.
 */
class RewriteExecTrie
{
 public:
  /** Add needle to this trie, associating it with the given rule index. */
  void addTerm(const Node& needle, size_t ruleIndex);
  /**
   * Find the first stored needle that matches n, i.e. needle * { vars -> subs }
   * = n for some substitution. If a match is found, vars and subs are set to
   * the matching substitution and the associated rule index is returned.
   * Returns a negative value if there is no match.
   */
  int64_t getMatch(const Node& n,
                   std::vector<Node>& vars,
                   std::vector<Node>& subs) const;

 private:
  /**
   * The children of this trie node, indexed by (operator or leaf, arity). This
   * matches the indexing scheme of expr::MatchTrie.
   */
  std::map<Node, std::map<uint64_t, RewriteExecTrie>> d_children;
  /** The variables that branch at this trie node. */
  std::vector<Node> d_vars;
  /** The rule index if this node is a terminal, or a negative value. */
  int64_t d_data = -1;
};

/**
 * The executable rewrite database. Holds all :exec rules and provides a single
 * entry point (rewrite) that applies them via one post-order traversal.
 */
class RewriteDbExec
{
 public:
  RewriteDbExec(NodeManager* nm);
  ~RewriteDbExec() {}

  /**
   * Add an :exec rule with left-hand side lhs and right-hand side rhs. If lhs
   * contains list variables, it must have the restricted form (f t1 s t2) as
   * described in the file header; otherwise lhs may be an arbitrary
   * application. This method is called by the auto-generated
   * addRewriteExecRules.
   */
  void addRule(ProofRewriteRule id, const Node& lhs, const Node& rhs);

  /** Are there no rules in this database? */
  bool empty() const { return d_rules.empty(); }

  /**
   * Apply the :exec rules to n. This performs a single post-order traversal of
   * n, attempting to rewrite each (otherwise unrewritten) subterm using the
   * trie. Returns the rewritten term, or n itself if nothing applied.
   */
  Node rewrite(const Node& n);

 private:
  /** Information stored for a single :exec rule. */
  struct ExecRule
  {
    /** The identifier of the rule (for tracing). */
    ProofRewriteRule d_id;
    /** Whether this is a (f t1 s t2) rule (as opposed to a direct pattern). */
    bool d_hasList;
    /** The list variable t1 that binds the prefix children (if d_hasList). */
    Node d_listVar1;
    /** The list variable t2 that binds the suffix children (if d_hasList). */
    Node d_listVar2;
    /** The right-hand side of the rule. */
    Node d_rhs;
  };
  /**
   * Try to apply a single :exec rule at the top symbol of n. Returns the
   * rewritten term, or the null node if no rule applies to n.
   */
  Node rewriteTop(const Node& n);
  /** Pointer to the node manager. */
  NodeManager* d_nm;
  /** All :exec rules, indexed by the rule indices stored in the tries. */
  std::vector<ExecRule> d_rules;
  /** A discrimination trie over the left-hand sides of no-list-var rules. */
  RewriteExecTrie d_direct;
  /** A discrimination trie over needles, one per top-level operator kind. */
  std::map<Kind, RewriteExecTrie> d_needleIndex;
};

}  // namespace rewriter
}  // namespace cvc5::internal

#endif /* CVC5__REWRITER__REWRITE_DB_EXEC__H */
