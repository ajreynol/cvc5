/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Trivial inst match generator class.
 */

#include "theory/quantifiers/ematching/inst_match_generator_trivial.h"

#include "smt/env.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_util.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

InstMatchGeneratorTrivial::InstMatchGeneratorTrivial(Env& env,
                                                     Trigger* tparent,
                                                     Node q,
                                                     Node pat)
    : IMGenerator(env, tparent),
      d_quant(q),
      d_pat(pat),
      d_terms(d_env.getUserContext())
{
  for (size_t i = 0, nchild = d_pat.getNumChildren(); i < nchild; i++)
  {
    Assert(d_pat[i].getKind() == Kind::INST_CONSTANT);
    d_varNum.push_back(d_pat[i].getAttribute(InstVarNumAttribute()));
  }
  TermDb* tdb = d_treg.getTermDatabase();
  d_op = tdb->getMatchOperator(d_pat);
  d_tvec.resize(d_quant[0].getNumChildren());
}

void InstMatchGeneratorTrivial::resetInstantiationRound()
{
  // do nothing
}

uint64_t InstMatchGeneratorTrivial::addInstantiations(InstMatch& m)
{
  TermDb* tdb = d_treg.getTermDatabase();
  TNodeTrie* tat = tdb->getTermArgTrie(d_op);
  if (tat == nullptr || d_qstate.isInConflict())
  {
    return 0;
  }
  // get the list of non-redundant terms from the arg trie of the operator
  std::vector<Node> list = tat->getLeaves(d_tvec.size());
  uint64_t addedLemmas = 0;
  Trace("trivial-trigger") << "Process trivial trigger " << d_pat
                           << ", #terms=" << list.size() << std::endl;
  size_t procTerms = 0;
  size_t tli = 0;
  size_t tlLimit = list.size();
  while (tli < tlLimit)
  {
    Node n = list[tli];
    ++tli;
    // if already considered this term
    if (d_terms.find(n) != d_terms.end())
    {
      continue;
    }
    Trace("trivial-trigger-debug") << "...check active " << n << std::endl;
    // should be relevant if it was indexed
    Assert(tdb->hasTermCurrent(n));
    ++procTerms;
    Assert(n.getNumChildren() == d_varNum.size());
    // it is an instantiation, map it based on the variable order
    for (size_t i = 0, nvars = d_varNum.size(); i < nvars; i++)
    {
      Assert(d_varNum[i] < n.getNumChildren());
      d_tvec[d_varNum[i]] = n[i];
    }
    if (sendInstantiation(d_tvec))
    {
      // now we can cache
      d_terms.insert(n);
      addedLemmas++;
    }
  }
  Trace("trivial-trigger") << "...lemmas/processed/total " << addedLemmas << "/"
                           << procTerms << "/" << list.size() << std::endl;
  return addedLemmas;
}

int InstMatchGeneratorTrivial::getActiveScore()
{
  TermDb* tdb = d_treg.getTermDatabase();
  size_t ngt = tdb->getNumGroundTerms(d_op);
  return static_cast<int>(ngt);
}

InferenceId InstMatchGeneratorTrivial::getInferenceId()
{
  return InferenceId::QUANTIFIERS_INST_E_MATCHING_TRIVIAL;
}

bool InstMatchGeneratorTrivial::isTrivialTrigger(const Node& pat)
{
  Assert(pat.getNumChildren() > 0);
  std::unordered_set<Node> children;
  // must each be unique inst constants
  for (size_t i = 0, nchild = pat.getNumChildren(); i < nchild; i++)
  {
    if (pat[i].getKind() != Kind::INST_CONSTANT)
    {
      return false;
    }
    if (!children.insert(pat[i]).second)
    {
      return false;
    }
  }
  return true;
}

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
