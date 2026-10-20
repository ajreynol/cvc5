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

#include "proof/incremental_proof_printer.h"

#include <unordered_set>

#include "options/io_utils.h"
#include "smt/assertions.h"

namespace cvc5::internal {
namespace proof {

IncrementalProofPrinter::IncrementalProofPrinter(Env& env,
                                                 std::ostream& out,
                                                 rewriter::RewriteDb* rdb)
    : EnvObj(env),
      d_out(out),
      d_atp(nodeManager()),
      d_eop(env, d_atp, rdb),
      d_eout(out, d_eop.getLetBinding(), "@t", true),
      d_userLevel(0),
      d_scriptLevel(0),
      d_numAsserts(0)
{
  // global options on out, as done by EoPrinter::print
  options::ioutils::applyOutputLanguage(out, Language::LANG_SMTLIB_V2_6);
  options::ioutils::applyPrintArithLitToken(out, true);
  options::ioutils::applyPrintSkolemDefinitions(out, true);
}

IncrementalProofPrinter::~IncrementalProofPrinter() {}

void IncrementalProofPrinter::notifyPush(smt::Assertions& as)
{
  // print the assertions of the current context before pushing
  printNewAssertions(as, as.getAssertionList().size());
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
  d_numAsserts = 0;
}

void IncrementalProofPrinter::printProof(std::shared_ptr<ProofNode> pfn,
                                         smt::Assertions& as)
{
  // The assumptions of the check-sat are the last entries of the assertion
  // list. We print the assertions before them.
  size_t nassumps = as.getAssumptions().size();
  size_t nasserts = as.getAssertionList().size();
  Assert(nasserts >= nassumps);
  printNewAssertions(as, nasserts - nassumps);
  ensureScopes();
  // the assumptions are only in scope for this proof
  bool hasAssumps = nassumps > 0;
  if (hasAssumps)
  {
    pushScope();
  }
  d_eop.printIncremental(
      d_eout, pfn, ProofScopeMode::DEFINITIONS_AND_ASSERTIONS);
  if (hasAssumps)
  {
    popScope();
  }
}

void IncrementalProofPrinter::printNewAssertions(smt::Assertions& as,
                                                 size_t end)
{
  if (end <= d_numAsserts)
  {
    return;
  }
  // partition into definitions and assertions, as done when constructing the
  // scopes of the final proof
  const context::CDList<Node>& al = as.getAssertionList();
  std::unordered_set<Node> defs = as.getCurrentAssertionListDefitions();
  std::vector<Node> definitions;
  std::vector<Node> assertions;
  for (size_t i = d_numAsserts; i < end; i++)
  {
    const Node& a = al[i];
    if (a.getKind() == Kind::EQUAL && defs.find(a) != defs.end())
    {
      definitions.push_back(a);
    }
    else
    {
      assertions.push_back(a);
    }
  }
  ensureScopes();
  d_eop.printAssumptions(d_eout, definitions, assertions);
  d_numAsserts = end;
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
  d_numAssertsStack.push_back(d_numAsserts);
  d_scriptLevel++;
}

void IncrementalProofPrinter::popScope()
{
  Assert(d_scriptLevel > 0);
  d_out << "(pop 1)" << std::endl;
  d_eop.popScriptScope();
  Assert(!d_numAssertsStack.empty());
  d_numAsserts = d_numAssertsStack.back();
  d_numAssertsStack.pop_back();
  d_scriptLevel--;
}

}  // namespace proof
}  // namespace cvc5::internal
