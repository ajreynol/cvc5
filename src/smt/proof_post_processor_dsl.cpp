/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for post-processing proof nodes for DSL rewrite reconstruction.
 */

#include "smt/proof_post_processor_dsl.h"

#include <algorithm>

#include "expr/nary_term_util.h"
#include "options/base_options.h"
#include "options/smt_options.h"
#include "proof/proof_ensure_closed.h"
#include "proof/proof_node_algorithm.h"
#include "proof/trust_id.h"
#include "smt/env.h"

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace smt {

namespace {

/**
 * Notification class that captures the substitution witnessing that the
 * conclusion of a given rewrite rule matches a term, ignoring the matches of
 * the conclusions of all other rules.
 */
class DslRuleMatch : public expr::NotifyMatch
{
 public:
  DslRuleMatch(rewriter::RewriteDb* db, ProofRewriteRule id)
      : d_found(false), d_db(db), d_id(id)
  {
  }
  bool notify(CVC5_UNUSED Node s,
              Node n,
              std::vector<Node>& vars,
              std::vector<Node>& subs) override
  {
    const std::vector<ProofRewriteRule>& ids = d_db->getRuleIdsForHead(n);
    if (std::find(ids.begin(), ids.end(), d_id) == ids.end())
    {
      // this is the conclusion of another rule, keep looking
      return true;
    }
    d_found = true;
    d_vars = vars;
    d_subs = subs;
    // we have what we came for, stop the search
    return false;
  }
  /** Whether the conclusion of the rule matched. */
  bool d_found;
  /** The variables of the rule that were bound, and the terms they matched. */
  std::vector<Node> d_vars;
  std::vector<Node> d_subs;

 private:
  rewriter::RewriteDb* d_db;
  ProofRewriteRule d_id;
};

}  // namespace

ProofPostprocessDsl::ProofPostprocessDsl(Env& env, rewriter::RewriteDb* rdb)
    : EnvObj(env), d_rdb(rdb), d_rdbPc(env, rdb)
{
  d_true = nodeManager()->mkConst(true);
  d_tmode = (options().proof.proofGranularityMode
             == options::ProofGranularityMode::DSL_REWRITE_STRICT)
                ? rewriter::TheoryRewriteMode::RESORT
                : rewriter::TheoryRewriteMode::STANDARD;
}

bool ProofPostprocessDsl::proveWithRule(CDProof* cdp,
                                        ProofRewriteRule id,
                                        const Node& eq)
{
  Assert(eq.getKind() == Kind::EQUAL);
  Trace("pp-dsl") << "...apply " << id << " to " << eq << std::endl;
  const rewriter::RewriteProofRule& rpr = d_rdb->getRule(id);
  // find the substitution witnessing that the conclusion of the rule matches
  DslRuleMatch dm(d_rdb, id);
  d_rdb->getMatches(eq[0], &dm);
  if (!dm.d_found)
  {
    Trace("pp-dsl") << "...fail, the rule does not match" << std::endl;
    return false;
  }
  // put the substitution in the order of the variable list of the rule, which
  // is the order the arguments of a DSL_REWRITE step are given in
  const std::vector<Node>& varList = rpr.getVarList();
  std::vector<Node> subs;
  for (const Node& v : varList)
  {
    const std::vector<Node>& mvars = dm.d_vars;
    std::vector<Node>::const_iterator it =
        std::find(mvars.begin(), mvars.end(), v);
    if (it == mvars.end())
    {
      Trace("pp-dsl") << "...fail, " << v << " was not bound" << std::endl;
      return false;
    }
    subs.push_back(dm.d_subs[std::distance(mvars.begin(), it)]);
  }
  // the rule must prove exactly the equality we are asked for
  if (rpr.getConclusionFor(subs) != eq)
  {
    Trace("pp-dsl") << "...fail, the rule concludes "
                    << rpr.getConclusionFor(subs) << std::endl;
    return false;
  }
  // The instantiated conditions of the rule are the premises of the step. We
  // add each as a trusted step, which we reconstruct in turn, since the
  // updater revisits the proof we add here.
  std::vector<Node> premises;
  for (const Node& c : rpr.getConditions())
  {
    Node ci = expr::narySubstitute(c, varList, subs);
    if (ci.isNull())
    {
      Trace("pp-dsl") << "...fail, could not instantiate " << c << std::endl;
      return false;
    }
    premises.push_back(ci);
  }
  for (const Node& p : premises)
  {
    if (!cdp->hasStep(p))
    {
      cdp->addTrustedStep(p, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
    }
  }
  std::vector<Node> args;
  args.push_back(rewriter::mkRewriteRuleNode(nodeManager(), id));
  args.insert(args.end(), subs.begin(), subs.end());
  cdp->addStep(eq, ProofRule::DSL_REWRITE, premises, args);
  Trace("pp-dsl") << "...success, with premises " << premises << std::endl;
  return true;
}

void ProofPostprocessDsl::reconstruct(
    std::vector<std::shared_ptr<ProofNode>>& pfs)
{
  if (pfs.empty())
  {
    return;
  }
  Trace("pp-dsl") << "Reconstruct proofs for " << pfs.size()
                  << " trusted steps..." << std::endl;
  // Run an updater for this callback. We do subproof merging, as we may
  // encounter "subgoals" of theory rewrites that are the same. Moreover,
  // since subproof merging is only in scope for a single run of an updater,
  // we tie the proofs in pfs together with an AND_INTRO step, if necessary.
  d_traversing.clear();
  ProofNodeUpdater pnu(d_env, *this, true);
  std::shared_ptr<ProofNode> pfn;
  if (pfs.size() > 1)
  {
    ProofNodeManager* pnm = d_env.getProofNodeManager();
    pfn = pnm->mkNode(ProofRule::AND_INTRO, pfs, {});
  }
  else
  {
    pfn = pfs[0];
  }
  Trace("pp-dsl-process") << "BEGIN update" << std::endl;
  pnu.process(pfn);
  Trace("pp-dsl-process") << "END update" << std::endl;
}

bool ProofPostprocessDsl::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                       CVC5_UNUSED const std::vector<Node>& fa,
                                       bool& continueUpdate)
{
  ProofRule id = pn->getRule();
  continueUpdate = true;
  // we should update if we
  // - Have rule TRUST or TRUST_THEORY_REWRITE,
  // - We have no premises
  // - We are not already recursively expanding >= 3 steps of the above form.
  // We check for the third criteria by tracking a d_traversing vector.
  if ((id == ProofRule::TRUST || id == ProofRule::TRUST_THEORY_REWRITE)
      && pn->getChildren().empty() && d_traversing.size() < 3)
  {
    Trace("pp-dsl-process") << "...push " << pn.get() << std::endl;
    // note that we may be pushing pn more than once, if it is updated from a
    // trust step to another trust step.
    d_traversing.push_back(pn);
    return true;
  }
  return false;
}

void ProofPostprocessDsl::finalize(std::shared_ptr<ProofNode> pn)
{
  // clean up d_traversing at post-traversal
  // note we may have pushed multiple copies of pn consecutively if a proof
  // was updated to another trust step.
  while (!d_traversing.empty() && d_traversing.back() == pn)
  {
    Trace("pp-dsl-process") << "...pop " << pn.get() << std::endl;
    d_traversing.pop_back();
  }
}

bool ProofPostprocessDsl::update(Node res,
                                 ProofRule id,
                                 CVC5_UNUSED const std::vector<Node>& children,
                                 const std::vector<Node>& args,
                                 CDProof* cdp,
                                 bool& continueUpdate)
{
  continueUpdate = false;
  Assert(id == ProofRule::TRUST || id == ProofRule::TRUST_THEORY_REWRITE);
  Assert(children.empty());
  Assert(!res.isNull());
  bool reqTrueElim = false;
  // if not an equality, make (= res true).
  if (res.getKind() != Kind::EQUAL)
  {
    res = res.eqNode(d_true);
    reqTrueElim = true;
  }
  TheoryId tid = THEORY_LAST;
  MethodId mid = MethodId::RW_REWRITE;
  rewriter::TheoryRewriteMode tm = d_tmode;
  // The rule the rewriter applied, if this step came from an executable RARE
  // rewrite. In that case we know which rule proves res and need not search.
  ProofRewriteRule execId = ProofRewriteRule::NONE;
  Trace("pp-dsl") << "Prove " << res << " from " << tid << " / " << mid
                  << ", in mode " << tm << std::endl;
  Trace("pp-dsl") << "...proof rule " << id << std::endl;
  // if theory rewrite, get diagnostic information
  if (id == ProofRule::TRUST_THEORY_REWRITE)
  {
    builtin::BuiltinProofRuleChecker::getTheoryId(args[1], tid);
    getMethodId(args[2], mid);
  }
  else if (id == ProofRule::TRUST)
  {
    TrustId trid;
    getTrustId(args[0], trid);
    Trace("pp-dsl") << "...trust id " << trid << std::endl;
    if (trid == TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE)
    {
      // If we are MACRO_THEORY_REWRITE_RCONS_SIMPLE, we do not use
      // theory rewrites. This policy ensures that macro theory rewrites are
      // disabled on rewrites which we use for their own reconstruction.
      tm = rewriter::TheoryRewriteMode::NEVER;
    }
    else if (trid == TrustId::THEORY_REWRITE_EXEC)
    {
      // The rewriter recorded which RARE rule it applied as the third argument
      // of the step.
      Assert(args.size() == 3);
      if (!rewriter::getRewriteRule(args[2], execId))
      {
        Assert(false) << "Missing rule id for " << trid;
      }
    }
  }
  int64_t recLimit = options().proof.proofRewriteRconsRecLimit;
  int64_t stepLimit = options().proof.proofRewriteRconsStepLimit;
  // If the step came from an executable RARE rewrite, we know which rule proves
  // it, hence we apply that rule directly instead of searching for a proof.
  // Otherwise, and if applying it fails, attempt to reconstruct the proof of
  // the equality into cdp using the rewrite database proof reconstructor.
  // We record the subgoals in d_subgoals.
  bool proved = false;
  if (execId != ProofRewriteRule::NONE)
  {
    proved = proveWithRule(cdp, execId, res);
    // Failing here means the rewriter reported that execId applied, while
    // applying it to the same equality here says that it does not, i.e. the
    // generated implementation of the executable rules does not agree with the
    // rules it was generated from. We fall back on searching for a proof, but
    // this is a bug and not a hard reconstruction problem, hence we are loud
    // about it rather than silently leaving a trusted step.
    if (!proved)
    {
      Assert(false) << "Executable rewrite rule " << execId
                    << " does not prove " << res;
      warning() << "WARNING: the executable rewrite rule " << execId
                << " does not prove " << res << std::endl;
    }
  }
  if (!proved)
  {
    proved = d_rdbPc.prove(cdp, res[0], res[1], recLimit, stepLimit, tm);
  }
  if (proved)
  {
    // we will update this again, in case the elaboration introduced
    // new trust steps
    continueUpdate = true;
    // If we made (= res true) above, conclude the original res.
    if (reqTrueElim)
    {
      cdp->addStep(res[0], ProofRule::TRUE_ELIM, {res}, {});
      res = res[0];
    }
    Trace("check-dsl") << "Check closed..." << std::endl;
    pfgEnsureClosed(options(), res, cdp, "check-dsl", "check dsl");
    // if successful, we update the proof
    return true;
  }
  // clean up traversing, since we are setting continueUpdate to false
  Assert(!d_traversing.empty());
  Trace("pp-dsl-process") << "...pop due to fail " << d_traversing.back().get()
                          << std::endl;
  d_traversing.pop_back();
  // otherwise no update
  return false;
}

}  // namespace smt
}  // namespace cvc5::internal
