/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Printer for the implementation of the executable rewrite database.
 */

#include "cvc5_private.h"

#ifndef CVC5__REWRITER__REWRITE_DB_EXEC_PRINTER__H
#define CVC5__REWRITER__REWRITE_DB_EXEC_PRINTER__H

#include <cvc5/cvc5_proof_rule.h>

#include <iosfwd>
#include <vector>

#include "expr/node.h"

namespace cvc5::internal {
namespace rewriter {

/** The information stored for a single :exec rule. */
struct ExecRule
{
  /** The identifier of the rule. */
  ProofRewriteRule d_id;
  /** The left-hand side of the rule. */
  Node d_lhs;
  /** The conditions of the rule (empty if unconditional). */
  std::vector<Node> d_conds;
  /** The right-hand side of the rule. */
  Node d_rhs;
};

/**
 * An index of the RARE rules marked with the :exec attribute.
 *
 * This exists only to generate the implementation of RewriteDbExec: it is
 * populated by the auto-generated addRewriteExecRules and read by
 * printRewriteDbExec below, both of which run only when `-o rare-db-exec` is
 * given. It is not used while solving, where the generated implementation
 * matches terms directly instead of consulting an index of rules.
 */
class ExecRuleIndex
{
 public:
  ExecRuleIndex() {}

  /**
   * Add an :exec rule with (possibly empty) conditions conds, left-hand side
   * lhs and right-hand side rhs. This method is called by the auto-generated
   * addRewriteExecRules.
   */
  void addRule(ProofRewriteRule id,
               const std::vector<Node>& conds,
               const Node& lhs,
               const Node& rhs);

  /** Get the rules of this index, in the order they were added. */
  const std::vector<ExecRule>& getRules() const { return d_rules; }

 private:
  /** The rules of this index. */
  std::vector<ExecRule> d_rules;
};

/**
 * Print to os the C++ implementation of the single step rewrite given by the
 * RARE rules marked with :exec, that is, the contents of rewrite_db_exec.cpp.
 *
 * The printed implementation tests the shape of a term with straight-line code
 * instead of consulting an index of rules, and instantiates the conditions and
 * right-hand side of a match on demand.
 *
 * This is invoked by `-o rare-db-exec`, and its output is installed by
 * contrib/install-rare-rewrites.
 */
void printRewriteDbExec(std::ostream& os, NodeManager* nm);

}  // namespace rewriter
}  // namespace cvc5::internal

#endif /* CVC5__REWRITER__REWRITE_DB_EXEC_PRINTER__H */
