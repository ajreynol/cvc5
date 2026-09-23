/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof generator for equalities proven by the rewrite database proof
 * reconstructor.
 */

#include "rewriter/rewrite_db_proof_generator.h"

#include "expr/term_context.h"
#include "proof/conv_proof_generator.h"
#include "proof/proof_node_algorithm.h"
#include "rewriter/basic_rewrite_rcons.h"
#include "rewriter/rewrite_db.h"
#include "smt/env.h"
#include "theory/evaluator.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace rewriter {

RewriteDbProofGenerator::RewriteDbProofGenerator(
    Env& env,
    RewriteDb* db,
    BasicRewriteRCons& trrc,
    const std::unordered_map<Node, ProvenInfo>& pcache,
    theory::Evaluator& eval,
    std::unordered_map<Node, Node>& evalCache)
    : EnvObj(env),
      d_db(db),
      d_trrc(trrc),
      d_pcache(pcache),
      d_eval(eval),
      d_evalCache(evalCache)
{
  d_true = nodeManager()->mkConst(true);
}

std::shared_ptr<ProofNode> RewriteDbProofGenerator::getProofFor(Node f)
{
  CDProof cdp(d_env);
  if (!ensureProof(&cdp, f))
  {
    return nullptr;
  }
  return cdp.getProofFor(f);
}

bool RewriteDbProofGenerator::hasProofFor(Node f)
{
  auto it = d_pcache.find(f);
  return it != d_pcache.end() && it->second.d_id != RewriteProofStatus::FAIL;
}

std::string RewriteDbProofGenerator::identify() const
{
  return "RewriteDbProofGenerator";
}

bool RewriteDbProofGenerator::ensureProof(CDProof* cdp, const Node& eqi)
{
  // note we could use single internal cdp to improve subproof sharing
  NodeManager* nm = nodeManager();
  std::unordered_map<TNode, bool> visited;
  std::unordered_map<TNode, std::vector<Node>> premises;
  std::unordered_map<TNode, std::vector<Node>> pfArgs;
  std::unordered_map<TNode, bool>::iterator it;
  bool inserted;
  std::unordered_map<Node, ProvenInfo>::const_iterator itd;
  std::vector<Node>::const_iterator itv;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(eqi);
  do
  {
    cur = visit.back();
    visit.pop_back();
    std::tie(it, inserted) = visited.emplace(cur, false);
    itd = d_pcache.find(cur);
    Assert(itd != d_pcache.end());
    const ProvenInfo& pcur = itd->second;
    Assert(cur.getKind() == Kind::EQUAL);
    if (inserted)
    {
      Trace("rpc-debug") << "Ensure proof for " << cur << std::endl;
      visit.push_back(cur);
      // may already have a proof rule from a previous call
      if (cdp->hasStep(cur))
      {
        it->second = true;
        Trace("rpc-debug") << "...already proven" << std::endl;
      }
      else
      {
        Assert(pcur.d_id != RewriteProofStatus::FAIL);
        Trace("rpc-debug") << "...proved via " << pcur.d_id << std::endl;
        if (pcur.d_id == RewriteProofStatus::REFL)
        {
          it->second = true;
          // trivial proof
          Assert(cur[0] == cur[1]);
          cdp->addStep(cur, ProofRule::REFL, {}, {cur[0]});
        }
        else if (pcur.d_id == RewriteProofStatus::EVAL)
        {
          it->second = true;
          // NOTE: this could just evaluate the equality itself
          Assert(cur.getKind() == Kind::EQUAL);
          std::vector<Node> transc;
          for (size_t i = 0; i < 2; ++i)
          {
            Node curv = doEvaluate(cur[i]);
            if (curv == cur[i])
            {
              continue;
            }
            Node eq = cur[i].eqNode(curv);
            // flip orientation for second child
            transc.push_back(i == 1 ? curv.eqNode(cur[i]) : eq);
            // trivial evaluation, add evaluation method id
            cdp->addStep(eq, ProofRule::EVALUATE, {}, {cur[i]});
          }
          if (transc.size() == 2)
          {
            // do transitivity if both sides evaluate
            cdp->addStep(cur, ProofRule::TRANS, transc, {});
          }
        }
        else
        {
          std::vector<Node>& ps = premises[cur];
          std::vector<Node>& pfac = pfArgs[cur];
          if (pcur.isInternalRule())
          {
            // premises are the steps, stored in d_vars
            ps.insert(ps.end(), pcur.d_vars.begin(), pcur.d_vars.end());
          }
          else
          {
            Assert(cur.getKind() == Kind::EQUAL);
            Assert(pcur.d_dslId != ProofRewriteRule::NONE);
            // add the DSL proof rule we used
            pfac.push_back(
                nm->mkConstInt(Rational(static_cast<uint32_t>(pcur.d_dslId))));
            if (pcur.d_id == RewriteProofStatus::DSL)
            {
              const RewriteProofRule& rpr = d_db->getRule(pcur.d_dslId);
              // compute premises based on the used substitution
              // build the substitution context
              const std::vector<Node>& vs = rpr.getVarList();
              Assert(pcur.d_vars.size() == vs.size());
              std::vector<Node> rsubs;
              // must order the variables to match order of rewrite rule
              for (const Node& v : vs)
              {
                itv = std::find(pcur.d_vars.begin(), pcur.d_vars.end(), v);
                size_t d = std::distance(pcur.d_vars.begin(), itv);
                Assert(d < pcur.d_subs.size());
                rsubs.push_back(pcur.d_subs[d]);
              }
              // get the conditions, store into premises of cur.
              if (!rpr.getObligations(vs, rsubs, ps))
              {
                DebugUnhandled() << "failed a side condition?";
                return false;
              }
              pfac.insert(pfac.end(), rsubs.begin(), rsubs.end());
            }
            else
            {
              Assert(pcur.d_id == RewriteProofStatus::THEORY_REWRITE);
              pfac.push_back(cur);
            }
          }
          // recurse on premises
          visit.insert(visit.end(), ps.begin(), ps.end());
        }
      }
    }
    else if (!it->second)
    {
      // Now, add the proof rule. We do this after its children proofs already
      // exist.
      it->second = true;
      Assert(premises.find(cur) != premises.end());
      std::vector<Node>& ps = premises[cur];
      // get the conclusion
      Node conc;
      RewriteProofStatus status = pcur.d_id;
      if (status == RewriteProofStatus::FLATTEN)
      {
        Kind ck = cur[0].getKind();
        status = (ck == Kind::ADD || ck == Kind::NONLINEAR_MULT)
                     ? RewriteProofStatus::ARITH_POLY_NORM
                     : RewriteProofStatus::ACI_NORM;
      }
      if (status == RewriteProofStatus::TRANS)
      {
        conc = ps[0][0].eqNode(ps.back()[1]);
        cdp->addStep(conc, ProofRule::TRANS, ps, {});
      }
      else if (status == RewriteProofStatus::CONG)
      {
        // get the appropriate CONG rule
        std::vector<Node> cargs;
        ProofRule cr = expr::getCongRule(cur[0], cargs);
        cdp->addStep(cur, cr, ps, cargs);
      }
      else if (status == RewriteProofStatus::CONG_EVAL)
      {
        // congruence + evaluation, given we are trying to prove
        //   (f t1 ... tn) == c
        // This tactic checks if t1 ... tn rewrite to constants c1 ... cn.
        // If so, we try to show subgoals
        //   t1 == c1 ... tn == cn
        // The final proof is a congruence step + evaluation:
        //   (f t1 ... tn) == (f c1 ... cn) == c.
        Node lhs = cur[0];
        std::vector<Node> lhsTgtc;
        if (cur[0].getMetaKind() == metakind::PARAMETERIZED)
        {
          lhsTgtc.push_back(cur[0].getOperator());
        }
        for (const Node& eq : pcur.d_vars)
        {
          Assert(eq.getKind() == Kind::EQUAL);
          lhsTgtc.push_back(eq[1]);
        }
        Node lhsTgt = nm->mkNode(cur[0].getKind(), lhsTgtc);
        Node rhs = doEvaluate(cur[1]);
        Assert(!rhs.isNull());
        Node eq1 = lhs.eqNode(lhsTgt);
        Node eq2 = lhsTgt.eqNode(rhs);
        std::vector<Node> transChildren = {eq1, eq2};
        // get the appropriate CONG rule
        std::vector<Node> cargs;
        ProofRule cr = expr::getCongRule(eq1[0], cargs);
        cdp->addStep(eq1, cr, ps, cargs);
        cdp->addStep(eq2, ProofRule::EVALUATE, {}, {lhsTgt});
        if (rhs != cur[1])
        {
          cdp->addStep(cur[1].eqNode(rhs), ProofRule::EVALUATE, {}, {cur[1]});
          transChildren.push_back(rhs.eqNode(cur[1]));
        }
        cdp->addStep(cur, ProofRule::TRANS, transChildren, {});
      }
      else if (status == RewriteProofStatus::TRUE_ELIM)
      {
        conc = ps[0][0];
        cdp->addStep(conc, ProofRule::TRUE_ELIM, ps, {});
      }
      else if (status == RewriteProofStatus::TRUE_INTRO)
      {
        conc = ps[0].eqNode(d_true);
        cdp->addStep(conc, ProofRule::TRUE_INTRO, ps, {});
      }
      else if (status == RewriteProofStatus::ABSORB)
      {
        cdp->addStep(cur, ProofRule::ABSORB, {}, {cur});
      }
      else if (status == RewriteProofStatus::ACI_NORM)
      {
        cdp->addStep(cur, ProofRule::ACI_NORM, {}, {cur});
      }
      else if (status == RewriteProofStatus::ARITH_POLY_NORM)
      {
        TypeNode tn =
            pcur.d_vars.empty() ? cur[0].getType() : cur[0][0].getType();
        bool isBitVec = (tn.isBitVector());
        ProofRule pr =
            isBitVec ? ProofRule::BV_POLY_NORM : ProofRule::ARITH_POLY_NORM;
        if (pcur.d_vars.empty())
        {
          cdp->addStep(cur, pr, {}, {cur});
        }
        else
        {
          ProofRule prr = isBitVec ? ProofRule::BV_POLY_NORM_EQ
                                   : ProofRule::ARITH_POLY_NORM_REL;
          cdp->addStep(pcur.d_vars[0], pr, {}, {pcur.d_vars[0]});
          cdp->addStep(cur, prr, {pcur.d_vars[0]}, {cur});
        }
      }
      else if (status == RewriteProofStatus::DSL_FIXED_POINT)
      {
        const RewriteProofRule& rpr = d_db->getRule(pcur.d_dslId);
        const std::vector<size_t>& path = rpr.getPathToContextVar();
        // We only want to rewrite on the relevant path. So for example
        // if our context is lambda x. (or C x), then we only apply
        // rewrites on the path that traverses the second child of
        // ors, recurisvely.
        bool emptyPath = path.empty();
        WithinPathTermContext wptc(path);
        TConvProofGenerator tcpg(d_env,
                                 nullptr,
                                 TConvPolicy::FIXPOINT,
                                 TConvCachePolicy::NEVER,
                                 "DslFixedPointTConv",
                                 emptyPath ? nullptr : &wptc);
        Trace("rpc-debug") << "Prove fixed point " << pcur.d_dslId
                           << " via:" << std::endl;
        Trace("rpc-debug") << "- path size is " << path.size() << std::endl;
        Trace("rpc-debug") << "- conclusion: " << cur << std::endl;
        size_t tc = 1;
        for (const Node& s : pcur.d_vars)
        {
          Trace("rpc-debug") << "  - step: " << s << std::endl;
          // Fixed-point steps are an explicit rewrite chain. Register them as
          // pre-rewrites so they are applied in the recorded order before
          // child rewriting changes the current redex.
          tcpg.addRewriteStep(
              s[0], s[1], cdp, true, TrustId::NONE, false, emptyPath ? 0 : tc);
          // the next rewrite should be applied at the depth that adds the
          // length of the path.
          tc += path.size();
        }
        std::shared_ptr<ProofNode> pfn = tcpg.getProofFor(cur);
        Assert(pfn != nullptr);
        cdp->addProof(pfn);
      }
      else if (status == RewriteProofStatus::DSL
               || status == RewriteProofStatus::THEORY_REWRITE)
      {
        Assert(pfArgs.find(cur) != pfArgs.end());
        Assert(pcur.d_dslId != ProofRewriteRule::NONE);
        const std::vector<Node>& args = pfArgs[cur];
        ProofRule pfr;
        if (status == RewriteProofStatus::DSL)
        {
          std::vector<Node> subs(args.begin() + 1, args.end());
          const RewriteProofRule& rpr = d_db->getRule(pcur.d_dslId);
          conc = rpr.getConclusionFor(subs);
          Trace("rpc-debug") << "Finalize proof for " << cur << std::endl;
          Trace("rpc-debug") << "Proved: " << cur << std::endl;
          Trace("rpc-debug") << "From: " << conc << std::endl;
          pfr = ProofRule::DSL_REWRITE;
          cdp->addStep(conc, pfr, ps, args);
        }
        else
        {
          Assert(status == RewriteProofStatus::THEORY_REWRITE);
          // Use the utility, possibly to do macro expansion.
          // We use a fresh CDProof to avoid duplicate substeps.
          CDProof cdpt(d_env);
          d_trrc.ensureProofForTheoryRewrite(&cdpt, pcur.d_dslId, cur);
          cdp->addProof(cdpt.getProofFor(cur));
        }
      }
    }
  } while (!visit.empty());
  return true;
}

Node RewriteDbProofGenerator::doEvaluate(const Node& n)
{
  // All terms evaluated here were evaluated during proof search, so this is
  // typically a cache lookup.
  auto [itv, inserted] = d_evalCache.emplace(n, Node());
  if (inserted)
  {
    itv->second = d_eval.eval(n, {}, {});
  }
  return itv->second;
}

}  // namespace rewriter
}  // namespace cvc5::internal
