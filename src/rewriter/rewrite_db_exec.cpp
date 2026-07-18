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
 */

#include "rewriter/rewrite_db_exec.h"

#include "expr/nary_term_util.h"
#include "rewriter/rewrites.h"

namespace cvc5::internal {
namespace rewriter {

/**
 * Notification class used to capture the first :exec rule whose left-hand side
 * matches a candidate term. On a match, it instantiates the right-hand side and
 * records the rule id, then stops the search.
 */
class RewriteExecNotify : public expr::NotifyMatch
{
 public:
  RewriteExecNotify(const RewriteDbExec& db) : d_db(db) {}
  bool notify(Node n,
              Node lhs,
              std::vector<Node>& vars,
              std::vector<Node>& subs) override
  {
    // lhs is the (stored) left-hand side that matches n under { vars -> subs }
    const RewriteDbExec::ExecRule& er = d_db.getRuleForLhs(lhs);
    Node res = expr::narySubstitute(er.d_rhs, vars, subs);
    if (res.isNull())
    {
      // could not construct the instantiated right-hand side; keep looking
      return true;
    }
    d_result = res;
    d_id = er.d_id;
    // stop at the first successful match
    return false;
  }
  /** The instantiated right-hand side, or null if no match was found. */
  Node d_result;
  /** The id of the rule that was applied. */
  ProofRewriteRule d_id = ProofRewriteRule::NONE;

 private:
  const RewriteDbExec& d_db;
};

RewriteDbExec::RewriteDbExec(NodeManager* nm) : d_nm(nm)
{
  // body is auto-generated from the RARE rules marked :exec
  addRewriteExecRules(nm, *this);
}

void RewriteDbExec::addRule(ProofRewriteRule id,
                            const Node& lhs,
                            const Node& rhs)
{
  // Multiple rules with an identical left-hand side would be ambiguous; keep
  // the first one added.
  if (d_ruleForLhs.find(lhs) != d_ruleForLhs.end())
  {
    return;
  }
  d_trie.addTerm(lhs);
  d_ruleForLhs[lhs] = ExecRule{id, rhs};
}

const RewriteDbExec::ExecRule& RewriteDbExec::getRuleForLhs(
    const Node& lhs) const
{
  std::map<Node, ExecRule>::const_iterator it = d_ruleForLhs.find(lhs);
  Assert(it != d_ruleForLhs.end());
  return it->second;
}

Node RewriteDbExec::rewrite(const Node& n, ProofRewriteRule& id)
{
  if (d_ruleForLhs.empty())
  {
    return Node::null();
  }
  RewriteExecNotify notify(*this);
  d_trie.getMatches(n, &notify);
  if (notify.d_result.isNull())
  {
    return Node::null();
  }
  id = notify.d_id;
  Trace("rewrite-exec") << "RewriteDbExec: " << n << std::endl
                        << "...via " << id << " rewrites to " << notify.d_result
                        << std::endl;
  return notify.d_result;
}

}  // namespace rewriter
}  // namespace cvc5::internal
