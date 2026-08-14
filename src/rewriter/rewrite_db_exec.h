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
   * Return the application of k to children, accounting for the children that
   * a :list variable bound to the empty sequence did not contribute. That is,
   * if children is empty we return the null terminator of k at type tn, and if
   * it is a singleton we return that child. Returns the null node if the
   * application could not be constructed, e.g. if k has no null terminator at
   * tn.
   *
   * This mirrors the corresponding case of expr::narySubstitute, which is how
   * the right-hand side of a rule with :list variables is instantiated.
   */
  Node mkNary(Kind k, const std::vector<Node>& children, const TypeNode& tn) const;

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
};

}  // namespace rewriter
}  // namespace cvc5::internal

#endif /* CVC5__REWRITER__REWRITE_DB_EXEC__H */
