/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof logger utility.
 */

#include "smt/proof_logger.h"

#include <sstream>

#include "options/base_options.h"
#include "options/main_options.h"
#include "printer/smt2/smt2_printer.h"
#include "proof/proof.h"
#include "proof/proof_node_manager.h"
#include "smt/print_benchmark.h"
#include "smt/proof_manager.h"

namespace cvc5::internal {

ProofLoggerCpc::ProofLoggerCpc(Env& env,
                               std::ostream& out,
                               smt::PfManager* pm,
                               smt::Assertions& as)
    : ProofLogger(env),
      d_isIncrementalDump(options().base.incrementalSolving
                          && options().driver.dumpProofs),
      d_printedExit(false),
      d_hasOutput(false),
      d_scriptLevel(0),
      d_printedInputs(&d_scriptCtx),
      d_printedLemmas(&d_scriptCtx),
      d_pm(pm),
      d_pnm(pm->getProofNodeManager()),
      d_as(as),
      d_atp(nodeManager()),
      // we use thresh 1 since terms may come incrementally and would benefit
      // from previous eager letification
      d_eop(env, d_atp, pm->getRewriteDatabase(), 1),
      d_eout(out, d_eop.getLetBinding(), "@t", false)
{
  Trace("pf-log-debug") << "Make proof logger" << std::endl;
  // global options on out
  options::ioutils::applyOutputLanguage(out, Language::LANG_SMTLIB_V2_6);
  options::ioutils::applyPrintArithLitToken(out, true);
  options::ioutils::applyPrintSkolemDefinitions(out, true);
}

ProofLoggerCpc::~ProofLoggerCpc()
{
  if (d_isIncrementalDump && d_hasOutput && !d_printedExit)
  {
    d_eout.getOStream() << "(exit)" << std::endl;
  }
}

void ProofLoggerCpc::notifyOutput() { d_hasOutput = true; }

void ProofLoggerCpc::notifyPush()
{
  if (!d_isIncrementalDump)
  {
    return;
  }
  std::ostream& out = d_eout.getOStream();
  out << "(push 1)" << std::endl;
  d_eop.pushCurrentContext();
  d_scriptCtx.push();
  ++d_scriptLevel;
  notifyOutput();
}

void ProofLoggerCpc::notifyPop()
{
  if (!d_isIncrementalDump)
  {
    return;
  }
  Assert(d_scriptLevel > 0);
  std::ostream& out = d_eout.getOStream();
  out << "(pop 1)" << std::endl;
  d_eop.popCurrentContext();
  d_scriptCtx.pop();
  --d_scriptLevel;
  notifyOutput();
}

void ProofLoggerCpc::notifyCheckSatResult(const Result& r)
{
  Result::Status s = r.getStatus();
  if (s != Result::SAT && s != Result::UNKNOWN)
  {
    // unsat responses are marked by the refutation in the proof
    return;
  }
  d_eout.getOStream() << "(echo \"" << (s == Result::SAT ? "sat" : "unknown")
                      << "\")" << std::endl;
  notifyOutput();
}

void ProofLoggerCpc::syncScriptContext()
{
  if (!d_isIncrementalDump)
  {
    return;
  }
  std::ostream& out = d_eout.getOStream();
  uint32_t level = userContext()->getLevel();
  if (level > 0)
  {
    --level;
  }
  while (d_scriptLevel < level)
  {
    out << "(push 1)" << std::endl;
    d_eop.pushCurrentContext();
    d_scriptCtx.push();
    ++d_scriptLevel;
    notifyOutput();
  }
  while (d_scriptLevel > level)
  {
    out << "(pop 1)" << std::endl;
    d_eop.popCurrentContext();
    d_scriptCtx.pop();
    --d_scriptLevel;
    notifyOutput();
  }
}

void ProofLoggerCpc::printDeclarationsOnce(
    const std::vector<Node>& definitions, const std::vector<Node>& assertions)
{
  printer::smt2::Smt2Printer alfp(printer::smt2::Variant::eo_variant);
  smt::PrintBenchmark pb(nodeManager(), &alfp, false, &d_atp);
  std::stringstream outDecl;
  std::stringstream outDef;
  options::ioutils::applyPrintArithLitToken(outDef, true);
  pb.printDeclarationsFrom(outDecl, outDef, definitions, assertions);

  std::ostream& out = d_eout.getOStream();
  auto emitUniqueLines = [&](const std::string& block) {
    std::stringstream ss(block);
    std::string line;
    while (std::getline(ss, line))
    {
      if (line.empty())
      {
        continue;
      }
      if (d_preambleLines.insert(line).second)
      {
        out << line << std::endl;
        notifyOutput();
      }
    }
  };
  emitUniqueLines(outDecl.str());
  emitUniqueLines(outDef.str());
}

void ProofLoggerCpc::logCnfPreprocessInputs(const std::vector<Node>& inputs)
{
  d_eout.getOStream() << "; log start" << std::endl;
  Trace("pf-log") << "; log: cnf preprocess input proof start" << std::endl;
  CDProof cdp(d_env);
  Node conc = nodeManager()->mkAnd(inputs);
  cdp.addTrustedStep(conc, TrustId::PREPROCESSED_INPUT, inputs, {});
  std::shared_ptr<ProofNode> pfn = cdp.getProofFor(conc);
  ProofScopeMode m = ProofScopeMode::DEFINITIONS_AND_ASSERTIONS;
  d_ppProof = d_pm->connectProofToAssertions(pfn, d_as, m);
  syncScriptContext();
  printDeclarationsOnce(d_ppProof->getArguments(),
                        d_ppProof->getChildren()[0]->getArguments());
  d_eop.printIncremental(d_eout, d_ppProof, m);
  notifyOutput();
  Trace("pf-log") << "; log: cnf preprocess input proof end" << std::endl;
}

void ProofLoggerCpc::logCnfPreprocessInputProofs(
    std::vector<std::shared_ptr<ProofNode>>& pfns)
{
  Trace("pf-log") << "; log: cnf preprocess input proof start" << std::endl;
  syncScriptContext();
  ProofScopeMode m = ProofScopeMode::DEFINITIONS_AND_ASSERTIONS;
  for (std::shared_ptr<ProofNode>& pfn : pfns)
  {
    Node res = pfn->getResult();
    if (d_isIncrementalDump && d_printedInputs.contains(res))
    {
      continue;
    }
    d_ppProof = d_pm->connectProofToAssertions(pfn, d_as, m);
    Assert(d_ppProof->getRule() == ProofRule::SCOPE);
    Assert(d_ppProof->getChildren()[0]->getRule() == ProofRule::SCOPE);
    printDeclarationsOnce(d_ppProof->getArguments(),
                          d_ppProof->getChildren()[0]->getArguments());
    d_eop.printIncremental(d_eout, d_ppProof, m);
    if (d_isIncrementalDump)
    {
      d_printedInputs.insert(res);
    }
    notifyOutput();
  }
  Trace("pf-log") << "; log: cnf preprocess input proof end" << std::endl;
}

void ProofLoggerCpc::logTheoryLemmaProof(std::shared_ptr<ProofNode>& pfn)
{
  Trace("pf-log") << "; log theory lemma proof start " << pfn->getResult()
                  << std::endl;
  d_lemmaPfs.emplace_back(pfn);
  std::shared_ptr<ProofNode> ppn = pfn->clone();
  ppn = d_pm->connectProofToAssertions(ppn, d_as, ProofScopeMode::NONE);
  if (!d_isIncrementalDump || !d_printedLemmas.contains(pfn->getResult()))
  {
    d_eop.printNext(d_eout, ppn);
    if (d_isIncrementalDump)
    {
      d_printedLemmas.insert(pfn->getResult());
    }
    notifyOutput();
  }
  Trace("pf-log") << "; log theory lemma proof end" << std::endl;
}

void ProofLoggerCpc::logTheoryLemma(const Node& n)
{
  Trace("pf-log") << "; log theory lemma start " << n << std::endl;
  std::shared_ptr<ProofNode> ptl =
      d_pnm->mkTrustedNode(TrustId::THEORY_LEMMA, {}, {}, n);
  d_lemmaPfs.emplace_back(ptl);
  if (!d_isIncrementalDump || !d_printedLemmas.contains(n))
  {
    d_eop.printNext(d_eout, ptl);
    if (d_isIncrementalDump)
    {
      d_printedLemmas.insert(n);
    }
    notifyOutput();
  }
  Trace("pf-log") << "; log theory lemma end" << std::endl;
}

void ProofLoggerCpc::logSatRefutation()
{
  Trace("pf-log") << "; log SAT refutation start" << std::endl;
  std::vector<std::shared_ptr<ProofNode>> premises;
  Assert(d_ppProof->getRule() == ProofRule::SCOPE);
  Assert(d_ppProof->getChildren()[0]->getRule() == ProofRule::SCOPE);
  std::shared_ptr<ProofNode> ppBody =
      d_ppProof->getChildren()[0]->getChildren()[0];
  premises.emplace_back(ppBody);
  premises.insert(premises.end(), d_lemmaPfs.begin(), d_lemmaPfs.end());
  Node f = nodeManager()->mkConst(false);
  std::shared_ptr<ProofNode> psr =
      d_pnm->mkNode(ProofRule::SAT_REFUTATION, premises, {}, f);
  d_eop.printNext(d_eout, psr);
  Trace("pf-log") << "; log SAT refutation end" << std::endl;
  notifyOutput();
  if (!d_isIncrementalDump)
  {
    d_eout.getOStream() << "(exit)" << std::endl;
    d_printedExit = true;
  }
}

void ProofLoggerCpc::logSatRefutationProof(std::shared_ptr<ProofNode>& pfn)
{
  Trace("pf-log") << "; log SAT refutation proof start" << std::endl;
  // connect to preprocessed
  std::shared_ptr<ProofNode> spf =
      d_pm->connectProofToAssertions(pfn, d_as, ProofScopeMode::NONE);
  d_eop.printNext(d_eout, spf);
  Trace("pf-log") << "; log SAT refutation proof end" << std::endl;
  notifyOutput();
  if (!d_isIncrementalDump)
  {
    d_eout.getOStream() << "(exit)" << std::endl;
    d_printedExit = true;
  }
}

}  // namespace cvc5::internal
