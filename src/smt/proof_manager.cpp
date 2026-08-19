/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The proof manager of the SMT engine.
 */

#include "smt/proof_manager.h"

#include "expr/subtype_elim_node_converter.h"
#include "options/base_options.h"
#include "options/main_options.h"
#include "options/smt_options.h"
#include "proof/alethe/alethe_node_converter.h"
#include "proof/alethe/alethe_post_processor.h"
#include "proof/alethe/alethe_printer.h"
#include "proof/dot/dot_printer.h"
#include "proof/eo/eo_printer.h"
#include "proof/lfsc/lfsc_post_processor.h"
#include "proof/lfsc/lfsc_printer.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "rewriter/rewrite_db.h"
#include "smt/assertions.h"
#include "smt/difficulty_post_processor.h"
#include "smt/env.h"
#include "smt/preprocess_proof_generator.h"
#include "smt/proof_logger.h"
#include "smt/proof_post_processor.h"
#include "smt/smt_solver.h"

using namespace cvc5::internal::rewriter;
namespace cvc5::internal {
namespace smt {

PfManager::PfManager(Env& env)
    : EnvObj(env),
      d_rewriteDb(nullptr),
      d_pchecker(nullptr),
      d_pnm(nullptr),
      d_pfpp(nullptr),
      d_pppg(nullptr),
      d_finalCb(env),
      d_finalizer(env, d_finalCb)
{
  // construct the rewrite db only if DSL rewrites are enabled
  if (options().proof.proofGranularityMode
          == options::ProofGranularityMode::DSL_REWRITE
      || options().proof.proofGranularityMode
             == options::ProofGranularityMode::DSL_REWRITE_STRICT)
  {
    d_rewriteDb.reset(new RewriteDb(nodeManager()));
    // maybe output rare rules?
    bool isNormalOut = isOutputOn(OutputTag::RARE_DB);
    bool isExpertOut = isOutputOn(OutputTag::RARE_DB_EXPERT);
    if (isNormalOut || isExpertOut)
    {
      if (options().proof.proofFormatMode != options::ProofFormatMode::CPC)
      {
        Warning()
            << "WARNING: Assuming --proof-format=cpc when printing the RARE "
               "database with -o rare-db(-expert)"
            << std::endl;
      }
      proof::EoNodeConverter atp(nodeManager());
      proof::EoPrinter eop(d_env, atp, d_rewriteDb.get());
      const std::map<ProofRewriteRule, RewriteProofRule>& rules =
          d_rewriteDb->getAllRules();
      for (const std::pair<const ProofRewriteRule, RewriteProofRule>& r : rules)
      {
        // only output if the signature level is what we want
        Level l = r.second.getSignatureLevel();
        if (l == Level::NORMAL && isNormalOut)
        {
          std::ostream& os = output(OutputTag::RARE_DB);
          eop.printDslRule(os, r.first);
        }
        else if (l == Level::EXPERT && isExpertOut)
        {
          std::ostream& os = output(OutputTag::RARE_DB_EXPERT);
          eop.printDslRule(os, r.first);
        }
      }
    }
  }

  // enable the proof checker and the proof node manager
  d_pchecker.reset(
      new ProofChecker(statisticsRegistry(),
                       options().proof.proofCheck,
                       static_cast<uint32_t>(options().proof.proofPedantic),
                       d_rewriteDb.get()));
  d_pnm.reset(new ProofNodeManager(env.getNodeManager(),
                                   env.getOptions(),
                                   env.getRewriter(),
                                   d_pchecker.get()));
  // Now, initialize the proof postprocessor with the environment.
  // By default the post-processor will update all assumptions, which
  // can lead to SCOPE subproofs of the form
  //   A
  //  ...
  //   B1    B2
  //  ...   ...
  // ------------
  //      C
  // ------------- SCOPE [B1, B2]
  // B1 ^ B2 => C
  //
  // where A is an available assumption from outside the scope (note
  // that B1 was an assumption of this SCOPE subproof but since it could
  // be inferred from A, it was updated). This shape is problematic for
  // the Alethe reconstruction, so we disable the update of scoped
  // assumptions (which would disable the update of B1 in this case).
  d_pfpp = std::make_unique<ProofPostprocess>(
      env,
      d_rewriteDb.get(),
      options().proof.proofFormatMode != options::ProofFormatMode::ALETHE);

  // add rules to eliminate here
  if (options().proof.proofGranularityMode
      != options::ProofGranularityMode::MACRO)
  {
    d_pfpp->setEliminateRule(ProofRule::MACRO_SR_EQ_INTRO);
    d_pfpp->setEliminateRule(ProofRule::MACRO_SR_PRED_INTRO);
    d_pfpp->setEliminateRule(ProofRule::MACRO_SR_PRED_ELIM);
    d_pfpp->setEliminateRule(ProofRule::MACRO_SR_PRED_TRANSFORM);
    // Alethe does not require chain multiset resolution to be expanded,
    // LFSC requires it to be expanded.
    if ((options().proof.proofFormatMode != options::ProofFormatMode::ALETHE
         && !options().proof.proofChainMRes)
        || options().proof.proofFormatMode == options::ProofFormatMode::LFSC)
    {
      d_pfpp->setEliminateRule(ProofRule::CHAIN_M_RESOLUTION);
    }
    d_pfpp->setEliminateRule(ProofRule::MACRO_ARITH_SCALE_SUM_UB);
    if (options().proof.proofGranularityMode
        != options::ProofGranularityMode::REWRITE)
    {
      d_pfpp->setEliminateRule(ProofRule::SUBS);
      d_pfpp->setEliminateRule(ProofRule::MACRO_REWRITE);
      // if in a DSL rewrite mode
      if (options().proof.proofGranularityMode
          != options::ProofGranularityMode::THEORY_REWRITE)
      {
        // this eliminates theory rewriting steps with finer-grained DSL rules
        d_pfpp->setEliminateAllTrustedRules();
      }
    }
    // theory-specific lazy proof reconstruction
    d_pfpp->setEliminateRule(ProofRule::MACRO_STRING_INFERENCE);
    d_pfpp->setEliminateRule(ProofRule::MACRO_BV_BITBLAST);
    // we only try to eliminate TRUST if not macro level
    d_pfpp->setEliminateRule(ProofRule::TRUST);
  }
  d_false = nodeManager()->mkConst(false);

  d_pppg = std::make_unique<PreprocessProofGenerator>(
      d_env, userContext(), "smt::PreprocessProofGenerator");
}

PfManager::~PfManager() {}

// TODO: Remove in favor of `std::erase_if` with C++ 20+ (see cvc5-wishues#137).
template <class T, class Alloc, class Pred>
constexpr typename std::vector<T, Alloc>::size_type erase_if(
    std::vector<T, Alloc>& c, Pred pred)
{
  typename std::vector<T, Alloc>::iterator it =
      std::remove_if(c.begin(), c.end(), pred);
  typename std::vector<T, Alloc>::size_type r = std::distance(it, c.end());
  c.erase(it, c.end());
  return r;
}

void PfManager::startProofLogging(std::ostream& out, Assertions& as)
{
  // by default, CPC proof logger
  d_plog.reset(new ProofLoggerCpc(d_env, out, this, as));
}

std::shared_ptr<ProofNode> PfManager::connectProofToAssertions(
    std::shared_ptr<ProofNode> pfn, Assertions& as, ProofScopeMode scopeMode)
{
  // Note this assumes that connectProofToAssertions is only called once per
  // unsat response. This method would need to cache its result otherwise.
  Trace("smt-proof")
      << "SolverEngine::connectProofToAssertions(): get proof body...\n";

  if (TraceIsOn("smt-proof-debug"))
  {
    Trace("smt-proof-debug")
        << "SolverEngine::connectProofToAssertions(): Proof node for false:\n";
    Trace("smt-proof-debug") << *pfn.get() << std::endl;
    Trace("smt-proof-debug") << "=====" << std::endl;
  }
  std::vector<Node> assertions;
  getAssertions(as, assertions);

  if (TraceIsOn("smt-proof"))
  {
    Trace("smt-proof")
        << "SolverEngine::connectProofToAssertions(): get free assumptions..."
        << std::endl;
    std::vector<Node> fassumps;
    expr::getFreeAssumptions(pfn.get(), fassumps);
    Trace("smt-proof") << "SolverEngine::connectProofToAssertions(): initial "
                          "free assumptions are:\n";
    for (const Node& a : fassumps)
    {
      Trace("smt-proof") << "- " << a << std::endl;
    }

    Trace("smt-proof")
        << "SolverEngine::connectProofToAssertions(): assertions are:\n";
    for (const Node& n : assertions)
    {
      Trace("smt-proof") << "- " << n << std::endl;
    }
    Trace("smt-proof") << "=====" << std::endl;
  }
  // do initial process of pfn
  prepareFinalProof(pfn);

  Trace("smt-proof")
      << "SolverEngine::connectProofToAssertions(): postprocess...\n";
  Assert(d_pfpp != nullptr);
  // Note that in incremental mode, we cannot set assertions here, as it
  // permits the postprocessor to merge subproofs at a higher user context
  // level into proofs that are used in a lower user context level.
  if (!options().base.incrementalSolving)
  {
    d_pfpp->setAssertions(assertions, false);
  }
  d_pfpp->process(pfn, d_pppg.get());
  // repeat the analysis on the fully elaborated proof
  analyzeUnrewrite(pfn, false);

  switch (scopeMode)
  {
    case ProofScopeMode::NONE:
    {
      return pfn;
    }
    // Now make the final scope(s), which ensure(s) that the only open leaves
    // of the proof are the assertions (and definitions). If we are pruning
    // the input, we will try to minimize the used assertions (and definitions).
    case ProofScopeMode::UNIFIED:
    {
      Trace("smt-proof") << "SolverEngine::connectProofToAssertions(): make "
                            "unified scope...\n";
      return d_pnm->mkScope(
          pfn, assertions, true, options().proof.proofPruneInput);
    }
    case ProofScopeMode::DEFINITIONS_AND_ASSERTIONS:
    {
      Trace("smt-proof")
          << "SolverEngine::connectProofToAssertions(): make split scope...\n";
      // To support proof pruning for nested scopes, we need to:
      // 1. Minimize assertions of closed unified scope.
      std::vector<Node> unifiedAssertions;
      getAssertions(as, unifiedAssertions);
      Pf pf = d_pnm->mkScope(
          pfn, unifiedAssertions, true, options().proof.proofPruneInput);
      // if this is violated, there is unsoundness since we have shown
      // false that does not depend on the input.
      AlwaysAssert(pf->getRule() == ProofRule::SCOPE);
      // 2. Extract minimum unified assertions from the scope node.
      std::unordered_set<Node> minUnifiedAssertions;
      minUnifiedAssertions.insert(pf->getArguments().cbegin(),
                                  pf->getArguments().cend());
      // 3. Split those assertions into minimized definitions and assertions.
      std::vector<Node> minDefinitions;
      std::vector<Node> minAssertions;
      getDefinitionsAndAssertions(as, minDefinitions, minAssertions);
      std::function<bool(Node)> predicate = [&minUnifiedAssertions](Node n) {
        return minUnifiedAssertions.find(n) == minUnifiedAssertions.cend();
      };
      erase_if(minDefinitions, predicate);
      erase_if(minAssertions, predicate);
      // 4. Extract proof from unified scope and encapsulate it with split
      // scopes introducing minimized definitions and assertions.
      return d_pnm->mkNode(
          ProofRule::SCOPE,
          {d_pnm->mkNode(ProofRule::SCOPE, pf->getChildren(), minAssertions)},
          minDefinitions);
    }
    default: Unreachable();
  }
}

void PfManager::prepareFinalProof(std::shared_ptr<ProofNode> pfn)
{
  if (!options().proof.proofUnrewrite)
  {
    return;
  }
  Trace("pf-urw-debug") << "Final proof is " << *pfn.get() << std::endl;
  std::shared_ptr<ProofNode> cur;
  std::vector<std::shared_ptr<ProofNode>> toProcess;
  toProcess.push_back(pfn);
  std::map<Node, std::vector<std::shared_ptr<ProofNode>>> amap;
  std::map<Node, size_t> amapProcessed;
  Trace("pf-urw") << "Look at proofs of CNF inputs" << std::endl;
  // expand the preprocess links
  do
  {
    cur = toProcess.back();
    toProcess.pop_back();
    expr::getFreeAssumptionsMap(cur, amap);
    for (const std::pair<const Node, std::vector<std::shared_ptr<ProofNode>>>&
             p : amap)
    {
      Node f = p.first;
      size_t start = amapProcessed[f];
      size_t end = p.second.size();
      if (start == end)
      {
        continue;
      }
      std::shared_ptr<ProofNode> cpfn = d_pppg->getProofFor(f);
      if (cpfn == nullptr || cpfn->getRule() == ProofRule::ASSUME)
      {
        Trace("pf-urw-debug") << "* Input: " << f << std::endl;
        continue;
      }
      Trace("pf-urw-debug") << "* Derived: " << f << std::endl;
      Trace("pf-urw-debug") << "Its proof is " << *cpfn.get() << std::endl;
      for (size_t i = start; i < end; i++)
      {
        d_pnm->updateNode(p.second[i].get(), cpfn.get());
      }
      amapProcessed[f] = end;
      toProcess.push_back(cpfn);
    }
  } while (!toProcess.empty());
  Trace("pf-urw-debug") << "Final proof is now " << *pfn.get() << std::endl;
  analyzeUnrewrite(pfn, true);
}

namespace {
/**
 * Is r a step whose purpose is to justify rewriting, i.e. a rewrite step or
 * one of the congruence/transitivity steps that glue rewrite steps together?
 */
bool isRewriteRule(ProofRule r)
{
  switch (r)
  {
    case ProofRule::MACRO_REWRITE:
    case ProofRule::MACRO_SR_EQ_INTRO:
    case ProofRule::MACRO_SR_PRED_INTRO:
    case ProofRule::MACRO_SR_PRED_ELIM:
    case ProofRule::MACRO_SR_PRED_TRANSFORM:
    case ProofRule::THEORY_REWRITE:
    case ProofRule::DSL_REWRITE:
    case ProofRule::EVALUATE:
    case ProofRule::ARITH_POLY_NORM:
    case ProofRule::ENCODE_EQ_INTRO:
    case ProofRule::CONG:
    case ProofRule::NARY_CONG:
    case ProofRule::HO_CONG:
    case ProofRule::TRANS:
    case ProofRule::REFL:
    case ProofRule::SYMM: return true;
    default: break;
  }
  return false;
}
/**
 * Is r a step that glues rewrite steps into a proof of an equality?
 */
bool isRewriteGlueRule(ProofRule r)
{
  switch (r)
  {
    case ProofRule::CONG:
    case ProofRule::NARY_CONG:
    case ProofRule::HO_CONG:
    case ProofRule::TRANS:
    case ProofRule::REFL:
    case ProofRule::SYMM: return true;
    default: break;
  }
  return false;
}

/**
 * Is pn a *rewriting* proof, i.e. a proof of an equality all of whose leaves
 * are rewrite steps? This distinguishes the congruence/transitivity steps that
 * assemble a rewrite proof from the ones that assemble a congruence closure
 * explanation, which look identical rule-wise but have assumptions as leaves.
 */
bool isRewriteProof(ProofNode* pn, std::unordered_map<ProofNode*, bool>& cache)
{
  std::vector<ProofNode*> visit{pn};
  while (!visit.empty())
  {
    ProofNode* cur = visit.back();
    auto it = cache.find(cur);
    if (it != cache.end())
    {
      visit.pop_back();
      continue;
    }
    ProofRule r = cur->getRule();
    if (!isRewriteRule(r) && !isRewriteGlueRule(r))
    {
      cache[cur] = false;
      visit.pop_back();
      continue;
    }
    bool allDone = true;
    bool res = true;
    for (const std::shared_ptr<ProofNode>& c : cur->getChildren())
    {
      auto itc = cache.find(c.get());
      if (itc == cache.end())
      {
        allDone = false;
        visit.push_back(c.get());
      }
      else if (!itc->second)
      {
        res = false;
      }
    }
    if (allDone)
    {
      cache[cur] = res;
      visit.pop_back();
    }
  }
  return cache[pn];
}
}  // namespace

void PfManager::analyzeUnrewrite(std::shared_ptr<ProofNode> pfn, bool isPre)
{
  if (!options().proof.proofUnrewrite)
  {
    return;
  }
  std::shared_ptr<ProofNode> cur;
  if (isPre)
  {
    // Partition the refutation into:
    // (1) the Boolean skeleton, i.e. the maximal prefix of the proof from the
    // root that uses only Boolean rules, which are agnostic to the content of
    // the theory literals they operate on,
    // (2) the frontier proofs "nbProofs" beneath that skeleton, which are
    // either theory lemmas (closed proofs) or input lemmas (proofs of
    // preprocessed formulas from the input assertions).
    //
    // Note this classification is only meaningful before post-processing,
    // which connects the theory lemmas to the input assertions. We hold on to
    // the frontier proofs, which the post-processor updates in place, so that
    // the same partition can be measured on the elaborated proof.
    d_urwTlProofs.clear();
    d_urwIlProofs.clear();
    d_urwIlUnrwProofs.clear();
    d_urwIlAnyUnrwProofs.clear();
    d_urwIlFrac.clear();
    d_urwAtoms.clear();
    d_urwSkeleton.clear();
    std::unordered_set<ProofNode*> visited;
    std::vector<std::shared_ptr<ProofNode>> visit;
    std::vector<std::shared_ptr<ProofNode>> nbProofs;
    visit.push_back(pfn);
    do
    {
      cur = visit.back();
      visit.pop_back();
      if (visited.find(cur.get()) == visited.end())
      {
        visited.insert(cur.get());
        if (expr::isBooleanRule(cur->getRule()))
        {
          d_urwSkeleton.push_back(cur);
          const std::vector<std::shared_ptr<ProofNode>>& cs =
              cur->getChildren();
          visit.insert(visit.end(), cs.begin(), cs.end());
        }
        else
        {
          nbProofs.push_back(cur);
        }
      }
    } while (!visit.empty());

    std::unordered_set<TNode> tlVisited;
    d_urwTlAtoms.clear();
    for (std::shared_ptr<ProofNode>& p : nbProofs)
    {
      Trace("pf-urw") << "*** Frontier: " << p->getResult() << std::endl;
      std::vector<Node> fas;
      expr::getFreeAssumptions(p.get(), fas);
      if (fas.empty())
      {
        Trace("pf-urw") << "--> theory lemma" << std::endl;
        d_urwTlProofs.push_back(p);
        expr::getTheoryAtoms(p->getResult(), d_urwTlAtoms, tlVisited);
      }
      else
      {
        Trace("pf-urw") << "--> input lemma via " << fas << std::endl;
        d_urwIlProofs.push_back(p);
      }
    }
    // An atom occurring in an input lemma but in no theory lemma is
    // "unrewritable": the SAT solver treated it as an opaque literal, hence
    // the rewriting that produced it was not required by the refutation.
    for (std::shared_ptr<ProofNode>& p : d_urwIlProofs)
    {
      std::unordered_set<Node> atoms;
      std::unordered_set<TNode> av;
      expr::getTheoryAtoms(p->getResult(), atoms, av);
      size_t nurw = 0;
      size_t natoms = 0;
      for (TNode a : atoms)
      {
        // Boolean constants are not atoms we could keep in unrewritten form;
        // in particular a preprocessing step that derives false outright must
        // keep its rewriting.
        if (a.isConst())
        {
          continue;
        }
        natoms++;
        if (d_urwTlAtoms.find(a) == d_urwTlAtoms.end())
        {
          Trace("pf-urw-debug") << "- pure input atom " << a << std::endl;
          d_urwAtoms.insert(a);
          nurw++;
        }
      }
      Trace("pf-urw") << "  " << nurw << " / " << natoms
                      << " atoms are unrewritable" << std::endl;
      if (nurw > 0)
      {
        d_urwIlAnyUnrwProofs.push_back(p);
        d_urwIlFrac[p] = double(nurw) / double(natoms);
        if (nurw == natoms)
        {
          d_urwIlUnrwProofs.push_back(p);
        }
      }
    }
  }
  // Measure the sizes of the three regions on the current form of the proof.
  std::unordered_set<ProofNode*> tlVisitedPf, ilVisitedPf, urwVisitedPf,
      anyUrwVisitedPf, allVisitedPf, skelVisitedPf;
  double estRemovable = 0.0;
  for (std::shared_ptr<ProofNode>& p : d_urwTlProofs)
  {
    countProofNodes(p, tlVisitedPf);
  }
  for (std::shared_ptr<ProofNode>& p : d_urwIlProofs)
  {
    countProofNodes(p, ilVisitedPf);
  }
  for (std::shared_ptr<ProofNode>& p : d_urwIlUnrwProofs)
  {
    countProofNodes(p, urwVisitedPf);
  }
  for (std::shared_ptr<ProofNode>& p : d_urwIlAnyUnrwProofs)
  {
    countProofNodes(p, anyUrwVisitedPf);
    std::unordered_set<ProofNode*> pv;
    countProofNodes(p, pv);
    estRemovable += d_urwIlFrac[p] * double(pv.size());
  }
  for (std::shared_ptr<ProofNode>& p : d_urwSkeleton)
  {
    skelVisitedPf.insert(p.get());
  }
  countProofNodes(pfn, allVisitedPf);
  size_t nodesInputOnly = 0;
  for (ProofNode* p : ilVisitedPf)
  {
    if (tlVisitedPf.find(p) == tlVisitedPf.end())
    {
      nodesInputOnly++;
    }
  }
  // How much of each region is spent justifying rewriting? Nodes reachable
  // from both an input lemma and a theory lemma are attributed to the input.
  size_t rwInput = 0;
  size_t rwTheory = 0;
  size_t rwTotal = 0;
  size_t rwpInput = 0;
  size_t rwpTheory = 0;
  size_t rwpTotal = 0;
  std::unordered_map<ProofNode*, bool> rwpCache;
  for (ProofNode* p : allVisitedPf)
  {
    bool isRwp = isRewriteProof(p, rwpCache);
    bool isRw = isRewriteRule(p->getRule());
    if (!isRw && !isRwp)
    {
      continue;
    }
    bool inInput = ilVisitedPf.find(p) != ilVisitedPf.end();
    bool inTheory = tlVisitedPf.find(p) != tlVisitedPf.end();
    if (isRw)
    {
      rwTotal++;
      rwInput += inInput ? 1 : 0;
      rwTheory += (!inInput && inTheory) ? 1 : 0;
    }
    if (isRwp)
    {
      rwpTotal++;
      rwpInput += inInput ? 1 : 0;
      rwpTheory += (!inInput && inTheory) ? 1 : 0;
    }
  }
  // count the atoms of the input lemmas on the current proof
  std::unordered_set<Node> ilAtoms;
  std::unordered_set<TNode> ilVisited;
  for (std::shared_ptr<ProofNode>& p : d_urwIlProofs)
  {
    expr::getTheoryAtoms(p->getResult(), ilAtoms, ilVisited);
  }
  size_t ilCountTl = 0;
  size_t ilCount = 0;
  for (TNode ila : ilAtoms)
  {
    if (ila.isConst())
    {
      continue;
    }
    if (d_urwTlAtoms.find(ila) != d_urwTlAtoms.end())
    {
      ilCountTl++;
    }
    else
    {
      ilCount++;
    }
  }
  // For each unrewritable atom, find the terms it is rewritten *from* within
  // the input lemmas. If an atom has a single preimage, the rewrite proof
  // deriving it can be dropped and the atom kept in its original form
  // everywhere. If it has several, the rewriting is doing real work: it is
  // merging distinct input atoms into one SAT literal, and dropping it would
  // break the resolution steps that connect them.
  // A rewrite proof of l = a' is typically a TRANS chain, whose links also
  // conclude an equality with a' on one side. Only the maximal node of a chain
  // gives a genuine preimage, so we skip nodes having a parent that concludes
  // an equality with the same atom.
  // Atoms of every frontier lemma, not just the input ones: the same
  // renaming applies to an atom a theory lemma derives by rewriting, as long
  // as every producer of the atom rewrites it from the same term.
  std::unordered_set<Node> frontierAtoms(d_urwTlAtoms.begin(),
                                         d_urwTlAtoms.end());
  {
    std::unordered_set<TNode> av;
    for (std::shared_ptr<ProofNode>& p : d_urwIlProofs)
    {
      expr::getTheoryAtoms(p->getResult(), frontierAtoms, av);
    }
  }
  std::map<ProofNode*, std::vector<ProofNode*>> parents;
  for (ProofNode* p : allVisitedPf)
  {
    for (const std::shared_ptr<ProofNode>& c : p->getChildren())
    {
      parents[c.get()].push_back(p);
    }
  }
  std::map<Node, std::unordered_set<Node>> preimage;
  std::map<Node, std::vector<ProofNode*>> preimagePf;
  for (ProofNode* p : allVisitedPf)
  {
    Node c = p->getResult();
    if (c.getKind() != Kind::EQUAL)
    {
      continue;
    }
    for (size_t i = 0; i < 2; i++)
    {
      if (frontierAtoms.find(c[i]) == frontierAtoms.end() || c[1 - i] == c[i])
      {
        continue;
      }
      bool subsumed = false;
      for (ProofNode* par : parents[p])
      {
        Node pc = par->getResult();
        if (pc.getKind() == Kind::EQUAL && (pc[0] == c[i] || pc[1] == c[i]))
        {
          subsumed = true;
          break;
        }
      }
      // The atom must be replaced by another atom that does not mention it:
      // substituting a literal by a formula would change the propositional
      // structure the resolution steps above depend on.
      if (expr::isBooleanConnective(c[1 - i])
          || expr::hasSubterm(c[1 - i], c[i]))
      {
        continue;
      }
      // Renaming the atom to a literal the refutation already uses would
      // merge two SAT literals, changing the set representation of the
      // clauses the resolution steps operate on.
      if (frontierAtoms.find(c[1 - i]) != frontierAtoms.end())
      {
        continue;
      }
      if (!subsumed)
      {
        preimage[c[i]].insert(c[1 - i]);
        preimagePf[c[i]].push_back(p);
      }
    }
  }
  size_t urwPre0 = 0;
  size_t urwPre1 = 0;
  size_t urwPreM = 0;
  std::unordered_set<ProofNode*> removable;
  std::unordered_set<ProofNode*> removableRoots;
  std::unordered_map<Node, Node> subs;
  std::unordered_map<Node, Node> subsWide;
  for (const Node& a : frontierAtoms)
  {
    std::map<Node, std::unordered_set<Node>>::iterator itp = preimage.find(a);
    if (itp != preimage.end() && itp->second.size() == 1)
    {
      subsWide[a] = *itp->second.begin();
    }
  }
  for (const Node& a : d_urwAtoms)
  {
    std::map<Node, std::unordered_set<Node>>::iterator itp = preimage.find(a);
    if (itp == preimage.end())
    {
      // the atom was already in the input in this form, nothing to remove
      urwPre0++;
      continue;
    }
    if (itp->second.size() > 1)
    {
      Trace("pf-urw") << "  atom " << a << " has " << itp->second.size()
                      << " preimages " << itp->second << std::endl;
      urwPreM++;
      continue;
    }
    urwPre1++;
    subs[a] = *itp->second.begin();
    for (ProofNode* pf : preimagePf[a])
    {
      removableRoots.insert(pf);
      if (!removable.insert(pf).second)
      {
        continue;
      }
      for (const std::shared_ptr<ProofNode>& c : pf->getChildren())
      {
        countProofNodes(c, removable);
      }
    }
  }
  // Nodes in a removable rewrite proof may also be reachable from a part of
  // the proof we are keeping, in which case removing them saves nothing. Walk
  // the proof again without descending into the removable roots to find what
  // survives, and discount it.
  std::unordered_set<ProofNode*> kept;
  {
    std::vector<ProofNode*> visit{pfn.get()};
    while (!visit.empty())
    {
      ProofNode* cur = visit.back();
      visit.pop_back();
      if (removableRoots.find(cur) != removableRoots.end()
          || !kept.insert(cur).second)
      {
        continue;
      }
      for (const std::shared_ptr<ProofNode>& c : cur->getChildren())
      {
        visit.push_back(c.get());
      }
    }
  }
  size_t removableExcl = 0;
  for (ProofNode* p : removable)
  {
    if (kept.find(p) == kept.end())
    {
      removableExcl++;
    }
  }
  // Now actually perform the transformation and report what it achieved. We
  // first try renaming every atom with a unique preimage anywhere in the
  // refutation, which also reaches the rewriting done inside theory lemmas,
  // and fall back to the input-only atoms if that does not replay.
  size_t nodesAfter = 0;
  size_t urwOk = 0;
  size_t nsubs = 0;
  bool inputOnly = options().proof.proofUnrewriteInputOnly;
  std::unordered_map<Node, Node>& subsUse = inputOnly ? subs : subsWide;
  if (!isPre && !subsUse.empty())
  {
    std::shared_ptr<ProofNode> npfn = tryUnrewrite(pfn, subsUse, preimagePf);
    if (npfn == nullptr && !inputOnly && !subs.empty())
    {
      npfn = tryUnrewrite(pfn, subs, preimagePf);
    }
    if (npfn != nullptr)
    {
      // the transformation must not introduce new open assumptions
      std::vector<Node> fa0, fa1;
      expr::getFreeAssumptions(pfn.get(), fa0);
      expr::getFreeAssumptions(npfn.get(), fa1);
      std::unordered_set<Node> fs0(fa0.begin(), fa0.end());
      bool assumpOk = true;
      for (const Node& a : fa1)
      {
        if (fs0.find(a) == fs0.end())
        {
          Trace("pf-urw") << "new assumption " << a << std::endl;
          assumpOk = false;
          break;
        }
      }
      if (assumpOk)
      {
        std::unordered_set<ProofNode*> nv;
        countProofNodes(npfn, nv);
        nodesAfter = nv.size();
        nsubs = subsUse.size();
        urwOk = 1;
        Trace("pf-urw") << "unrewrite: " << allVisitedPf.size() << " -> "
                        << nodesAfter << " nodes" << std::endl;
        // install the converted proof, so that it is what we check and print
        d_pnm->updateNode(pfn.get(), npfn.get());
      }
    }
  }
  // A single machine-readable summary line, see --trace=pf-urw-summary.
  Trace("pf-urw-summary")
      << "(unrewrite-summary :stage " << (isPre ? "pre" : "post")
      << " :nodes-total " << allVisitedPf.size() << " :nodes-skeleton "
      << skelVisitedPf.size() << " :nodes-theory-lemmas " << tlVisitedPf.size()
      << " :nodes-input-lemmas " << ilVisitedPf.size()
      << " :nodes-input-lemmas-only " << nodesInputOnly
      << " :nodes-input-lemmas-unrw " << urwVisitedPf.size()
      << " :nodes-input-lemmas-any-unrw " << anyUrwVisitedPf.size()
      << " :est-removable " << size_t(estRemovable) << " :rw-total "
      << rwTotal << " :rw-input " << rwInput << " :rw-theory " << rwTheory
      << " :rwp-total " << rwpTotal << " :rwp-input " << rwpInput
      << " :rwp-theory " << rwpTheory << " :urw-atoms " << d_urwAtoms.size()
      << " :urw-pre0 " << urwPre0 << " :urw-pre1 " << urwPre1
      << " :urw-pre-multi " << urwPreM << " :urw-removable "
      << removable.size() << " :urw-removable-excl " << removableExcl
      << " :urw-applied " << urwOk << " :urw-nodes-after " << nodesAfter
      << " :urw-subs " << nsubs << " :urw-subs-wide " << subsWide.size()
      << " :theory-lemmas " << d_urwTlProofs.size() << " :input-lemmas "
      << d_urwIlProofs.size() << " :input-lemmas-full-unrw "
      << d_urwIlUnrwProofs.size() << " :atoms-theory " << d_urwTlAtoms.size()
      << " :atoms-input " << ilAtoms.size() << " :atoms-input-shared "
      << ilCountTl << " :atoms-input-only " << ilCount << ")" << std::endl;
}

std::shared_ptr<ProofNode> PfManager::tryUnrewrite(
    std::shared_ptr<ProofNode> pfn,
    std::unordered_map<Node, Node> subs,
    const std::map<Node, std::vector<ProofNode*>>& preimagePf)
{
  // The renaming must be injective and must not map a term it also maps from,
  // otherwise it would merge two SAT literals or chase one into another.
  std::unordered_set<Node> images;
  std::vector<Node> bad;
  for (const std::pair<const Node, Node>& sp : subs)
  {
    if (subs.find(sp.second) != subs.end() || !images.insert(sp.second).second)
    {
      bad.push_back(sp.first);
    }
  }
  for (const Node& b : bad)
  {
    subs.erase(b);
  }
  // A step we cannot replay costs us the atoms it mentions, not the whole
  // transformation: drop them and try again.
  for (size_t i = 0; i < 8 && !subs.empty(); i++)
  {
    std::unordered_set<ProofNode*> roots;
    for (const std::pair<const Node, Node>& sp : subs)
    {
      std::map<Node, std::vector<ProofNode*>>::const_iterator itp =
          preimagePf.find(sp.first);
      if (itp != preimagePf.end())
      {
        roots.insert(itp->second.begin(), itp->second.end());
      }
    }
    std::unordered_set<Node> failAtoms;
    std::shared_ptr<ProofNode> np =
        applyUnrewrite(pfn.get(), subs, roots, failAtoms);
    if (np != nullptr && np->getResult() == pfn->getResult())
    {
      return np;
    }
    if (failAtoms.empty())
    {
      return nullptr;
    }
    Trace("pf-urw") << "unrewrite: retry without " << failAtoms.size()
                    << " of " << subs.size() << " atoms" << std::endl;
    for (const Node& a : failAtoms)
    {
      subs.erase(a);
    }
  }
  return nullptr;
}

std::shared_ptr<ProofNode> PfManager::applyUnrewrite(
    ProofNode* pn,
    const std::unordered_map<Node, Node>& subs,
    const std::unordered_set<ProofNode*>& cutRoots,
    std::unordered_set<Node>& failAtoms)
{
  std::vector<Node> ks;
  std::vector<Node> vs;
  for (const std::pair<const Node, Node>& sp : subs)
  {
    ks.push_back(sp.first);
    vs.push_back(sp.second);
  }
  std::unordered_map<Node, Node> scache;
  std::unordered_map<ProofNode*, std::shared_ptr<ProofNode>> cache;
  std::vector<ProofNode*> visit{pn};
  while (!visit.empty())
  {
    ProofNode* cur = visit.back();
    if (cache.find(cur) != cache.end())
    {
      visit.pop_back();
      continue;
    }
    // A node proving (= l a') where we keep the atom in its form l becomes a
    // reflexivity step, which discards its entire rewrite proof.
    if (cutRoots.find(cur) != cutRoots.end())
    {
      Node res = cur->getResult();
      Assert(res.getKind() == Kind::EQUAL);
      std::unordered_map<Node, Node>::const_iterator its = subs.find(res[1]);
      Node l = (its != subs.end() && its->second == res[0]) ? res[0] : res[1];
      cache[cur] = d_pnm->mkNode(ProofRule::REFL, {}, {l}, l.eqNode(l));
      Assert(d_pnm->getChecker()->checkDebug(ProofRule::REFL, {}, {l})
             == l.eqNode(l));
      visit.pop_back();
      continue;
    }
    bool allDone = true;
    bool childFail = false;
    std::vector<std::shared_ptr<ProofNode>> cch;
    for (const std::shared_ptr<ProofNode>& c : cur->getChildren())
    {
      std::unordered_map<ProofNode*, std::shared_ptr<ProofNode>>::iterator itc =
          cache.find(c.get());
      if (itc == cache.end())
      {
        allDone = false;
        visit.push_back(c.get());
      }
      else if (itc->second == nullptr)
      {
        childFail = true;
      }
      else
      {
        cch.push_back(itc->second);
      }
    }
    if (!allDone)
    {
      continue;
    }
    visit.pop_back();
    if (childFail)
    {
      cache[cur] = nullptr;
      continue;
    }
    Node res = cur->getResult();
    Node cres = res.substitute(ks.begin(), ks.end(), vs.begin(), vs.end());
    if (cur->getRule() == ProofRule::ASSUME)
    {
      // an assumption cannot be renamed, it is fixed by the input
      cache[cur] = cres == res ? d_pnm->mkAssume(res) : nullptr;
      continue;
    }
    std::vector<Node> cargs;
    for (const Node& a : cur->getArguments())
    {
      cargs.push_back(a.substitute(ks.begin(), ks.end(), vs.begin(), vs.end()));
    }
    // Check the replayed step explicitly: mkNode trusts the expected
    // conclusion unless proof checking is eager, which would let an unsound
    // renaming through.
    std::vector<Node> cconc;
    for (const std::shared_ptr<ProofNode>& c : cch)
    {
      cconc.push_back(c->getResult());
    }
    std::shared_ptr<ProofNode> np;
    // Ask what the step proves rather than whether it proves cres: some rule
    // checkers echo back the expected conclusion when they cannot recompute
    // it, which would let an inconsistent renaming through.
    Node checked =
        d_pnm->getChecker()->checkDebug(cur->getRule(), cconc, cargs);
    if (!checked.isNull() && checked == cres)
    {
      np = d_pnm->mkNode(cur->getRule(), cch, cargs, cres);
    }
    if (np == nullptr)
    {
      Trace("pf-urw-debug") << "unrewrite failed at " << cur->getRule() << " "
                            << cres << std::endl;
      // record which renamed atoms this step involves, so the caller can drop
      // them and try again
      std::unordered_set<Node> ats;
      std::unordered_set<TNode> av;
      expr::getTheoryAtoms(res, ats, av);
      for (const Node& a : ats)
      {
        if (subs.find(a) != subs.end())
        {
          failAtoms.insert(a);
        }
      }
      for (const Node& a : cur->getArguments())
      {
        std::unordered_set<Node> ats2;
        std::unordered_set<TNode> av2;
        expr::getTheoryAtoms(a, ats2, av2);
        for (const Node& a2 : ats2)
        {
          if (subs.find(a2) != subs.end())
          {
            failAtoms.insert(a2);
          }
        }
      }
    }
    cache[cur] = np;
  }
  return cache[pn];
}

void PfManager::countProofNodes(std::shared_ptr<ProofNode> pfn,
                                std::unordered_set<ProofNode*>& visited)
{
  std::vector<std::shared_ptr<ProofNode>> visit;
  std::shared_ptr<ProofNode> cur;
  visit.push_back(pfn);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur.get()) == visited.end())
    {
      visited.insert(cur.get());
      const std::vector<std::shared_ptr<ProofNode>>& cs = cur->getChildren();
      visit.insert(visit.end(), cs.begin(), cs.end());
    }
  } while (!visit.empty());
}

void PfManager::checkFinalProof(std::shared_ptr<ProofNode> pfn)
{
  // take stats and check pedantic
  d_finalCb.initializeUpdate();
  d_finalizer.process(pfn);

  std::stringstream serr;
  bool wasPedanticFailure = d_finalCb.wasPedanticFailure(serr);
  if (wasPedanticFailure)
  {
    AlwaysAssert(!wasPedanticFailure)
        << "ProofPostprocess::process: pedantic failure:" << std::endl
        << serr.str();
  }
}

void PfManager::printProof(std::ostream& out,
                           std::shared_ptr<ProofNode> fp,
                           options::ProofFormatMode mode,
                           ProofScopeMode scopeMode,
                           const std::map<Node, std::string>& assertionNames)
{
  Trace("smt-proof") << "PfManager::printProof: start " << mode << std::endl;
  // We don't want to invalidate the proof nodes in fp, since these may be
  // reused in further check-sat calls, or they may be used again if the
  // user asks for the proof again (in non-incremental mode). We don't need to
  // clone if the printing below does not modify the proof, which is the case
  // for proof formats Eunoia and NONE.
  if (mode != options::ProofFormatMode::CPC
      && mode != options::ProofFormatMode::NONE)
  {
    fp = fp->clone();
  }

  // according to the proof format, post process and print the proof node
  if (mode == options::ProofFormatMode::DOT)
  {
    proof::DotPrinter dotPrinter(d_env);
    dotPrinter.print(out, fp.get());
  }
  else if (mode == options::ProofFormatMode::CPC)
  {
    proof::EoNodeConverter atp(nodeManager());
    proof::EoPrinter eop(d_env, atp, d_rewriteDb.get());
    eop.print(out, fp, scopeMode);
  }
  else if (mode == options::ProofFormatMode::ALETHE)
  {
    options::ProofCheckMode oldMode = options().proof.proofCheck;
    d_pnm->getChecker()->setProofCheckMode(options::ProofCheckMode::NONE);
    proof::AletheNodeConverter anc(nodeManager(),
                                   options().proof.proofAletheDefineSkolems,
                                   options().proof.proofAletheTesting);
    proof::AletheProofPostprocess vpfpp(d_env, anc);
    if (vpfpp.process(fp))
    {
      proof::AletheProofPrinter vpp(d_env, anc);
      vpp.print(out, fp, assertionNames);
    }
    else
    {
      out << "(error " << vpfpp.getError() << ")";
    }
    d_pnm->getChecker()->setProofCheckMode(oldMode);
  }
  else if (mode == options::ProofFormatMode::LFSC)
  {
    Assert(fp->getRule() == ProofRule::SCOPE);
    proof::LfscNodeConverter ltp(nodeManager());
    proof::LfscProofPostprocess lpp(d_env, ltp);
    lpp.process(fp);
    proof::LfscPrinter lp(d_env, ltp, d_rewriteDb.get());
    lp.print(out, fp.get());
  }
  else
  {
    // otherwise, print using default printer
    // we call the printing method explicitly because we may want to print the
    // final proof node with conclusions
    fp->printDebug(out, options().proof.proofPrintConclusion);
  }
}

void PfManager::translateDifficultyMap(std::map<Node, Node>& dmap,
                                       Assertions& as)
{
  Trace("difficulty-proc") << "Translate difficulty start" << std::endl;
  Trace("difficulty") << "PfManager::translateDifficultyMap" << std::endl;
  if (dmap.empty())
  {
    return;
  }
  std::map<Node, Node> dmapp;
  Trace("difficulty-proc") << "Get ppAsserts" << std::endl;
  std::vector<Node> ppAsserts;
  SubtypeElimNodeConverter senc(nodeManager());
  for (const std::pair<const Node, Node>& ppa : dmap)
  {
    Node assertion = ppa.first;
    // proof may eliminate mixed arithmetic from the assertion
    if (options().proof.proofElimSubtypes)
    {
      assertion = senc.convert(ppa.first);
    }
    dmapp[assertion] = ppa.second;
    Trace("difficulty") << "  preprocess difficulty: " << assertion << " for "
                        << ppa.first << std::endl;
    // The difficulty manager should only report difficulty for preprocessed
    // assertions, or we will get an open proof below. This is ensured
    // internally by the difficuly manager.
    ppAsserts.push_back(ppa.first);
  }
  dmap.clear();
  Trace("difficulty-proc") << "Make SAT refutation" << std::endl;
  // assume a SAT refutation from all input assertions that were marked
  // as having a difficulty
  CDProof cdp(d_env);
  Node fnode = nodeManager()->mkConst(false);
  cdp.addStep(fnode, ProofRule::SAT_REFUTATION, ppAsserts, {});
  std::shared_ptr<ProofNode> pf = cdp.getProofFor(fnode);
  Trace("difficulty-proc") << "Get final proof" << std::endl;
  std::shared_ptr<ProofNode> fpf = connectProofToAssertions(pf, as);
  Trace("difficulty-debug") << "Final proof is " << *fpf.get() << std::endl;
  // We are typically a SCOPE here, although if we are not, then the proofs
  // have no free assumptions. If this is the case, then the only difficulty
  // was incremented on auxiliary lemmas added during preprocessing. Since
  // there are no dependencies, then the difficulty map is empty.
  if (fpf->getRule() != ProofRule::SCOPE)
  {
    return;
  }
  fpf = fpf->getChildren()[0];
  // analyze proof
  Assert(fpf->getRule() == ProofRule::SAT_REFUTATION);
  const std::vector<std::shared_ptr<ProofNode>>& children = fpf->getChildren();
  DifficultyPostprocessCallback dpc;
  ProofNodeUpdater dpnu(d_env, dpc);
  Trace("difficulty-proc") << "Compute accumulated difficulty" << std::endl;
  // For each child of SAT_REFUTATION, we increment the difficulty on all
  // "source" free assumptions (see DifficultyPostprocessCallback) by the
  // difficulty of the preprocessed assertion.
  for (const std::shared_ptr<ProofNode>& c : children)
  {
    Node res = c->getResult();
    Assert(dmapp.find(res) != dmapp.end())
        << "Could not find assumption " << res;
    Trace("difficulty-debug") << "  process: " << res << std::endl;
    Trace("difficulty-debug") << "  .dvalue: " << dmapp[res] << std::endl;
    Trace("difficulty-debug") << "  ..proof: " << *c.get() << std::endl;
    if (!dpc.setCurrentDifficulty(dmapp[res]))
    {
      continue;
    }
    dpnu.process(c);
  }
  // get the accumulated difficulty map from the callback
  dpc.getDifficultyMap(nodeManager(), dmap);
  Trace("difficulty-proc") << "Translate difficulty end" << std::endl;
}

ProofChecker* PfManager::getProofChecker() const { return d_pchecker.get(); }

ProofNodeManager* PfManager::getProofNodeManager() const { return d_pnm.get(); }

ProofLogger* PfManager::getProofLogger() const { return d_plog.get(); }

rewriter::RewriteDb* PfManager::getRewriteDatabase() const
{
  return d_rewriteDb.get();
}

PreprocessProofGenerator* PfManager::getPreprocessProofGenerator() const
{
  return d_pppg.get();
}

void PfManager::getAssertions(Assertions& as, std::vector<Node>& assertions)
{
  // note that the assertion list is always available
  const context::CDList<Node>& al = as.getAssertionList();
  for (const Node& a : al)
  {
    assertions.push_back(a);
  }
}

void PfManager::getDefinitionsAndAssertions(Assertions& as,
                                            std::vector<Node>& definitions,
                                            std::vector<Node>& assertions)
{
  const context::CDList<Node>& defs = as.getAssertionListDefinitions();
  for (const Node& d : defs)
  {
    // Keep treating (mutually) recursive functions as declarations +
    // assertions.
    if (d.getKind() == Kind::EQUAL)
    {
      definitions.push_back(d);
    }
  }
  const context::CDList<Node>& asserts = as.getAssertionList();
  for (const Node& a : asserts)
  {
    if (std::find(definitions.cbegin(), definitions.cend(), a)
        == definitions.cend())
    {
      assertions.push_back(a);
    }
  }
}

}  // namespace smt
}  // namespace cvc5::internal
