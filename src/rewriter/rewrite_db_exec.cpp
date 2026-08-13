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
#include "expr/node_manager.h"
#include "rewriter/rewrites.h"

namespace cvc5::internal {
namespace rewriter {

/**
 * Notification class used to collect the :exec rules whose left-hand side
 * matches a candidate term, together with the substitution witnessing the
 * match. The conditions and right-hand sides are instantiated later, on demand.
 */
class RewriteExecNotify : public expr::NotifyMatch
{
 public:
  RewriteExecNotify(const RewriteDbExec& db,
                    std::vector<RewriteDbExec::ExecMatch>& matches)
      : d_db(db), d_matches(matches)
  {
  }
  bool notify(CVC5_UNUSED Node n,
              Node lhs,
              std::vector<Node>& vars,
              std::vector<Node>& subs) override
  {
    // lhs is the (stored) left-hand side that matches n under { vars -> subs }
    const RewriteDbExec::ExecRule& er = d_db.getRuleForLhs(lhs);
    d_matches.push_back(RewriteDbExec::ExecMatch{er.d_id, &er, vars, subs});
    // continue, so that all matching rules are collected
    return true;
  }

 private:
  const RewriteDbExec& d_db;
  std::vector<RewriteDbExec::ExecMatch>& d_matches;
};

RewriteDbExec::RewriteDbExec(NodeManager* nm)
{
  // body is auto-generated from the RARE rules marked :exec
  addRewriteExecRules(nm, *this);
}

void RewriteDbExec::addRule(ProofRewriteRule id,
                            const std::vector<Node>& conds,
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
  d_ruleForLhs[lhs] = ExecRule{id, conds, rhs};
}

const RewriteDbExec::ExecRule& RewriteDbExec::getRuleForLhs(
    const Node& lhs) const
{
  std::map<Node, ExecRule>::const_iterator it = d_ruleForLhs.find(lhs);
  Assert(it != d_ruleForLhs.end());
  return it->second;
}

void RewriteDbExec::getMatches(const Node& n,
                               std::vector<ExecMatch>& matches) const
{
  if (d_ruleForLhs.empty())
  {
    return;
  }
  RewriteExecNotify notify(*this, matches);
  d_trie.getMatches(n, &notify);
  if (TraceIsOn("rewrite-exec") && !matches.empty())
  {
    Trace("rewrite-exec") << "RewriteDbExec: " << n << " matches:" << std::endl;
    for (const ExecMatch& m : matches)
    {
      Trace("rewrite-exec") << "...via " << m.d_id << std::endl;
    }
  }
}

size_t RewriteDbExec::getNumConditions(const ExecMatch& m) const
{
  return m.d_rule->d_conds.size();
}

Node RewriteDbExec::getCondition(const ExecMatch& m, size_t i) const
{
  Assert(i < m.d_rule->d_conds.size());
  return expr::narySubstitute(m.d_rule->d_conds[i], m.d_vars, m.d_subs);
}

Node RewriteDbExec::getResult(const ExecMatch& m) const
{
  return expr::narySubstitute(m.d_rule->d_rhs, m.d_vars, m.d_subs);
}

}  // namespace rewriter
}  // namespace cvc5::internal
