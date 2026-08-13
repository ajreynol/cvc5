/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Compiled implementation of the executable (interpreted) rewrite rules.
 *
 * This is the compiled counterpart of RewriteDbExec: it implements the same
 * single step rewrite by the RARE rules marked with the :exec attribute, but
 * as straight-line C++ that tests the shape of a term directly, instead of by
 * traversing a match trie at runtime.
 *
 * The bodies of the methods of this class are generated, not written by hand.
 * They are printed by `-o rare-db-exec` and installed into
 * rewrite_db_exec_compiled.cpp by contrib/install-rare-rewrites. Do not edit
 * that file; edit the RARE rules and regenerate it.
 */

#include "cvc5_private.h"

#ifndef CVC5__REWRITER__REWRITE_DB_EXEC_COMPILED__H
#define CVC5__REWRITER__REWRITE_DB_EXEC_COMPILED__H

#include <cvc5/cvc5_proof_rule.h>

#include <vector>

#include "expr/node.h"

namespace cvc5::internal {
namespace rewriter {

/**
 * An :exec rule whose left-hand side matched a term, as computed by the
 * compiled implementation below. The conditions and the right-hand side are
 * not instantiated here; use the getNumConditions/getCondition/getResult
 * methods of RewriteDbExecCompiled to instantiate them on demand.
 */
struct CompiledExecMatch
{
  /** The identifier of the rule that matched. */
  ProofRewriteRule d_id;
  /**
   * The terms that the variables of the rule were bound to, in the order the
   * variables first occur in a left-to-right traversal of its left-hand side.
   */
  std::vector<Node> d_subs;
};

/**
 * The compiled executable rewrite database. Provides the same interface as
 * RewriteDbExec, so that the two can be interchanged.
 */
class RewriteDbExecCompiled
{
 public:
  RewriteDbExecCompiled(NodeManager* nm);
  ~RewriteDbExecCompiled() {}

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
  void getMatches(const Node& n, std::vector<CompiledExecMatch>& matches) const;

  /** The number of conditions of the rule that m matched. */
  size_t getNumConditions(const CompiledExecMatch& m) const;
  /**
   * Get the i^th condition of the rule that m matched, instantiated for the
   * term m was computed for. Returns the null node if it could not be
   * constructed, in which case the match must be abandoned.
   */
  Node getCondition(const CompiledExecMatch& m, size_t i) const;
  /**
   * Get the right-hand side of the rule that m matched, instantiated for the
   * term m was computed for. Returns the null node if it could not be
   * constructed, in which case the match must be abandoned.
   */
  Node getResult(const CompiledExecMatch& m) const;

 private:
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

#endif /* CVC5__REWRITER__REWRITE_DB_EXEC_COMPILED__H */
