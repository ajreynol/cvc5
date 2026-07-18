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
#include "proof/conv_proof_generator.h"
#include "proof/method_id.h"
#include "rewriter/rewrites.h"
#include "theory/builtin/proof_checker.h"
#include "theory/rewriter.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace rewriter {

/**
 * Notification class used to capture the first :exec rule whose left-hand side
 * matches a candidate term and whose (instantiated) conditions all hold. On
 * success it instantiates the right-hand side, records the rule id and the
 * instantiated conditions, then stops the search.
 */
class RewriteExecNotify : public expr::NotifyMatch
{
 public:
  RewriteExecNotify(const RewriteDbExec& db, theory::Rewriter* rr, Node vtrue)
      : d_db(db), d_rr(rr), d_true(vtrue)
  {
  }
  bool notify(Node n,
              Node lhs,
              std::vector<Node>& vars,
              std::vector<Node>& subs) override
  {
    // lhs is the (stored) left-hand side that matches n under { vars -> subs }
    const RewriteDbExec::ExecRule& er = d_db.getRuleForLhs(lhs);
    // instantiate and check the conditions, verifying they rewrite to true
    std::vector<Node> condsInst;
    for (const Node& c : er.d_conds)
    {
      Node ci = expr::narySubstitute(c, vars, subs);
      if (ci.isNull() || d_rr->rewrite(ci) != d_true)
      {
        // condition does not hold; keep searching for another rule
        return true;
      }
      condsInst.push_back(ci);
    }
    Node res = expr::narySubstitute(er.d_rhs, vars, subs);
    if (res.isNull())
    {
      // could not construct the instantiated right-hand side; keep searching
      return true;
    }
    d_result = res;
    d_id = er.d_id;
    d_condsInst = condsInst;
    // stop at the first successful match
    return false;
  }
  /** The instantiated right-hand side, or null if no match was found. */
  Node d_result;
  /** The id of the rule that was applied. */
  ProofRewriteRule d_id = ProofRewriteRule::NONE;
  /** The instantiated conditions of the applied rule. */
  std::vector<Node> d_condsInst;

 private:
  const RewriteDbExec& d_db;
  theory::Rewriter* d_rr;
  Node d_true;
};

RewriteDbExec::RewriteDbExec(NodeManager* nm) : d_nm(nm)
{
  d_true = nm->mkConst(true);
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

Node RewriteDbExec::rewrite(const Node& n,
                            theory::Rewriter* rr,
                            TConvProofGenerator* tcpg,
                            ProofRewriteRule& id)
{
  if (d_ruleForLhs.empty())
  {
    return Node::null();
  }
  RewriteExecNotify notify(*this, rr, d_true);
  d_trie.getMatches(n, &notify);
  if (notify.d_result.isNull())
  {
    return Node::null();
  }
  id = notify.d_id;
  Trace("rewrite-exec") << "RewriteDbExec: " << n << std::endl
                        << "...via " << id << " rewrites to " << notify.d_result
                        << std::endl;
  if (tcpg != nullptr)
  {
    // Record the rewrite itself as a THEORY_REWRITE step (reconstructed by the
    // DSL proof machinery downstream).
    tcpg->addTheoryRewriteStep(n, notify.d_result, id);
    // For each (instantiated) condition, record a TRUST_THEORY_REWRITE step
    // proving that it holds, i.e. rewrites to true. These provide the premises
    // required when the THEORY_REWRITE step above is reconstructed.
    for (const Node& c : notify.d_condsInst)
    {
      Node ceq = c.eqNode(d_true);
      theory::TheoryId tid = theory::Theory::theoryOf(c);
      Node tidn =
          theory::builtin::BuiltinProofRuleChecker::mkTheoryIdNode(d_nm, tid);
      Node mid = mkMethodId(d_nm, MethodId::RW_REWRITE);
      tcpg->addRewriteStep(
          c, d_true, ProofRule::TRUST_THEORY_REWRITE, {}, {ceq, tidn, mid});
    }
  }
  return notify.d_result;
}

}  // namespace rewriter
}  // namespace cvc5::internal
