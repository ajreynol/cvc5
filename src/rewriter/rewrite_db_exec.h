/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The executable rewrite database.
 *
 * This implements a single step rewrite by the RARE rules marked with the
 * :exec attribute, which the rewriter applies as a last resort when the theory
 * rewriter leaves a term unchanged (see theory/rewriter.cpp).
 *
 * The implementation is compiled: it tests the shape of a term with
 * straight-line C++, rather than by traversing a match trie at runtime. The
 * bodies of the methods of this class are therefore generated, not written by
 * hand. They are printed by `-o rare-db-exec` (see rewrite_db_exec_printer.h)
 * and installed into rewrite_db_exec.cpp by contrib/install-rare-rewrites. Do
 * not edit that file; edit the RARE rules and regenerate it.
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
 * An :exec rule whose left-hand side matched a term. The conditions and the
 * right-hand side are not instantiated here; use the
 * getNumConditions/getCondition/getResult methods of RewriteDbExec to
 * instantiate them on demand, so that a match whose first condition fails does
 * not pay for instantiating the remaining ones.
 */
struct ExecMatch
{
  /** The identifier of the rule that matched. */
  ProofRewriteRule d_id;
  /**
   * The terms that the variables of the rule were bound to, in the order the
   * variables first occur in a left-to-right traversal of its left-hand side.
   */
  std::vector<Node> d_subs;
};

/** The executable rewrite database. */
class RewriteDbExec
{
 public:
  RewriteDbExec(NodeManager* nm);
  ~RewriteDbExec() {}

  /** Are there no rules in this database? */
  bool empty() const;

  /**
   * Compute the :exec rules whose left-hand side matches n and append them to
   * matches. Note that the conditions of the returned matches are *not*
   * checked here; it is the responsibility of the caller to verify that they
   * rewrite to true before using the right-hand side of a match.
   *
   * @param n The term to match.
   * @param matches The vector to append the matches to.
   */
  void getMatches(const Node& n, std::vector<ExecMatch>& matches) const;
  /**
   * Check that m is a match of n, that is, that instantiating the left-hand
   * side of the rule m names by the substitution m gives back n exactly.
   *
   * This validates the generated matching code against the rule it was
   * generated from: the shape tests, the indices read off an indexed operator,
   * the child range a :list variable was bound to and the binding of the
   * variables are all correct if and only if this holds. It is what makes the
   * generated code checkable rather than trusted, hence it is worth running
   * whenever we can afford to.
   */
  bool checkMatch(const Node& n, const ExecMatch& m) const;

  /** The number of conditions of the rule that m matched. */
  size_t getNumConditions(const ExecMatch& m) const;
  /**
   * Get the i^th condition of the rule that m matched, instantiated for the
   * term m was computed for. Returns the null node if it could not be
   * constructed, in which case the match must be abandoned.
   */
  Node getCondition(const ExecMatch& m, size_t i) const;
  /**
   * Get the right-hand side of the rule that m matched, instantiated for the
   * term m was computed for. Returns the null node if it could not be
   * constructed, in which case the match must be abandoned.
   */
  Node getResult(const ExecMatch& m) const;

 private:
  /**
   * The following are utilities used by the generated code, which are written
   * by hand rather than generated.
   */
  /**
   * Return the sequence of the children of n in [start, end), as the SEXPR
   * that a :list variable is bound to. Note this mirrors how the substitution
   * of a :list variable is represented in expr::narySubstitute.
   */
  Node mkListArg(const Node& n, size_t start, size_t end) const;
  /**
   * Instantiate the pattern p for the match m, where p is the right-hand side
   * or a condition of the rule that m matched.
   *
   * The patterns are stored as the RARE rules state them, that is, over the
   * encoding that RewriteDbNodeConverter defines. Instantiating one is hence
   * substituting the terms m bound, which expr::narySubstitute does including
   * the splicing of the :list variables, followed by mapping the result back
   * to the terms the rewriter uses, which toConcrete does.
   *
   * Returns the null node if the instance could not be constructed.
   */
  Node instantiate(const Node& p, const ExecMatch& m) const;
  /**
   * Return n with every application of an indexed operator that is stated
   * symbolically, i.e. as an APPLY_INDEXED_SYMBOLIC term, replaced by the
   * application of the operator it denotes. This is the inverse of the only
   * part of the encoding that the rewriter never builds itself.
   */
  Node toConcrete(const Node& n) const;
  /**
   * Build the conditions and right-hand sides of the rules. This is generated,
   * and called once by the constructor.
   */
  void initRules();

  /**
   * The generated matching routine, which getMatches above wraps so that the
   * matches it reports can be checked.
   */
  void getMatchesInternal(const Node& n, std::vector<ExecMatch>& matches) const;

  /** Pointer to the node manager. */
  NodeManager* d_nm;
  /**
   * The constants occurring in the rules, constructed once here so that the
   * generated code below can refer to them without consulting the node
   * manager on the rewrite hot path.
   */
  std::vector<Node> d_consts;
  /**
   * The types of the variables of the rules, likewise constructed once here.
   * A variable only matches a term whose type is comparable to its own, which
   * matters for the operators that are permissive for subtyping.
   */
  std::vector<TypeNode> d_types;
  /**
   * The variables of each rule, in the order the terms bound to them are given
   * in the substitution of a match of that rule.
   */
  std::map<ProofRewriteRule, std::vector<Node>> d_ruleVars;
  /** The left-hand side of each rule, as the RARE rules state it. */
  std::map<ProofRewriteRule, Node> d_ruleLhs;
  /** The conditions of each rule, as the RARE rules state them. */
  std::map<ProofRewriteRule, std::vector<Node>> d_ruleConds;
  /** The right-hand side of each rule, as the RARE rules state it. */
  std::map<ProofRewriteRule, Node> d_ruleRhs;
};

}  // namespace rewriter
}  // namespace cvc5::internal

#endif /* CVC5__REWRITER__REWRITE_DB_EXEC__H */
