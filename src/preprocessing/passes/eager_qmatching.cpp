/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Eager quantifiers matching
 */

#include "preprocessing/passes/eager_qmatching.h"

#include "expr/node_algorithm.h"
#include "preprocessing/assertion_pipeline.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

EagerQMatching::EagerQMatching(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "eager-qmatching")
{
}

PreprocessingPassResult EagerQMatching::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node a = (*assertionsToPreprocess)[i];
    if (a.getKind() == Kind::FORALL)
    {
      d_tlQuant.push_back(a);
    }
    processInternal(a);
  }
  // process instantiations
  std::vector<Node> newInst;
  std::map<Node, std::vector<Node> >::iterator itu;
  NodeManager* nm = nodeManager();
  size_t iter = 0;
  do
  {
    newInst.clear();
    Trace("eager-qm") << "Matching " << d_pinfo.size() << " patterns"
                      << std::endl;
    for (std::pair<const Node, PatInfo>& p : d_pinfo)
    {
      Node pat = p.first;
      itu = d_ufTerms.find(pat.getOperator());
      if (itu == d_ufTerms.end())
      {
        continue;
      }
      Node quant = p.second.d_quant;
      bool isTlQuant = std::find(d_tlQuant.begin(), d_tlQuant.end(), quant)
                       != d_tlQuant.end();
      size_t nuf = itu->second.size();
      for (size_t i = p.second.d_ufIndex; i < nuf; i++)
      {
        std::unordered_map<Node, Node> subs;
        if (!expr::match(pat, itu->second[i], subs))
        {
          continue;
        }
        // new instantiation
        std::vector<Node> svars;
        std::vector<Node> ssubs;
        for (const std::pair<const Node, Node>& s : subs)
        {
          svars.push_back(s.first);
          ssubs.push_back(s.second);
        }
        Node inst = quant[1].substitute(
            svars.begin(), svars.end(), ssubs.begin(), ssubs.end());
        if (!isTlQuant)
        {
          inst = nm->mkNode(Kind::IMPLIES, quant, inst);
        }
        newInst.push_back(inst);
      }
      p.second.d_ufIndex = nuf;
    }
    Trace("eager-qm") << "...got " << newInst.size() << " instantiations"
                      << std::endl;
    // add new instantiations, collect terms in them
    for (const Node& ni : newInst)
    {
      assertionsToPreprocess->push_back(
          ni, false, nullptr, TrustId::PREPROCESS_EAGER_QMATCHING, true);
      processInternal(ni);
    }
    iter++;
  } while (!newInst.empty() && iter < 3);
  return PreprocessingPassResult::NO_CONFLICT;
}

void EagerQMatching::processInternal(const Node& a)
{
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(a);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (!d_visited.insert(cur).second)
    {
      continue;
    }
    Kind ak = cur.getKind();
    if (ak == Kind::APPLY_UF)
    {
      d_ufTerms[cur.getOperator()].push_back(cur);
    }
    else if (ak == Kind::FORALL)
    {
      if (cur.getNumChildren() == 3)
      {
        for (const Node& curp : cur[2])
        {
          if (curp.getKind() == Kind::INST_PATTERN && curp.getNumChildren() == 1
              && curp[0].getKind() == Kind::APPLY_UF)
          {
            Trace("eager-qm-pat")
                << "Pattern: " << curp[0] << " for " << cur << std::endl;
            PatInfo& pi = d_pinfo[curp[0]];
            pi.d_quant = cur;
          }
        }
      }
    }
    visit.insert(visit.end(), cur.begin(), cur.end());
  } while (!visit.empty());
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
