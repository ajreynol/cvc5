/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for printing the proofs of an incremental run as a proof script.
 */

#include "smt/incremental_proof_printer.h"

#include "options/io_utils.h"

namespace cvc5::internal {
namespace smt {

IncrementalProofPrinter::IncrementalProofPrinter(Env& env,
                                                 std::ostream& out,
                                                 rewriter::RewriteDb* rdb)
    : EnvObj(env),
      d_out(out),
      d_atp(nodeManager()),
      d_eop(env, d_atp, rdb),
      d_eout(out, d_eop.getLetBinding(), "@t", true),
      d_userLevel(0),
      d_scriptLevel(0)
{
  // global options on out, as done by EoPrinter::print
  options::ioutils::applyOutputLanguage(out, Language::LANG_SMTLIB_V2_6);
  options::ioutils::applyPrintArithLitToken(out, true);
  options::ioutils::applyPrintSkolemDefinitions(out, true);
}

IncrementalProofPrinter::~IncrementalProofPrinter() {}

void IncrementalProofPrinter::notifyPush()
{
  d_userLevel++;
  // if we have started printing, mirror the push in the script
  if (d_scriptLevel > 0)
  {
    pushScope();
  }
}

void IncrementalProofPrinter::notifyPop()
{
  Assert(d_userLevel > 0);
  d_userLevel--;
  if (d_scriptLevel > 0)
  {
    popScope();
  }
}

void IncrementalProofPrinter::notifyResetAssertions()
{
  // pop all scopes, including the one enclosing the script
  while (d_scriptLevel > 0)
  {
    popScope();
  }
  d_userLevel = 0;
}

void IncrementalProofPrinter::notifyCheckSatResult(
    const Result& r, std::shared_ptr<ProofNode> pfn)
{
  Result::Status s = r.getStatus();
  if (s != Result::SAT && s != Result::UNSAT && s != Result::UNKNOWN)
  {
    return;
  }
  ensureScopes();
  if (s == Result::UNSAT)
  {
    Assert(pfn != nullptr);
    d_eop.printIncremental(
        d_eout, pfn, ProofScopeMode::DEFINITIONS_AND_ASSERTIONS);
  }
  d_out << "(echo \""
        << (s == Result::SAT ? "sat"
                             : (s == Result::UNSAT ? "unsat" : "unknown"))
        << "\")" << std::endl;
}

void IncrementalProofPrinter::ensureScopes()
{
  while (d_scriptLevel < d_userLevel + 1)
  {
    pushScope();
  }
}

void IncrementalProofPrinter::pushScope()
{
  d_out << "(push 1)" << std::endl;
  d_eop.pushScriptScope();
  d_scriptLevel++;
}

void IncrementalProofPrinter::popScope()
{
  Assert(d_scriptLevel > 0);
  d_out << "(pop 1)" << std::endl;
  d_eop.popScriptScope();
  d_scriptLevel--;
}

}  // namespace smt
}  // namespace cvc5::internal
