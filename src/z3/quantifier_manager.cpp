/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Quantifier reasoning for the ported Z3 core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_quantifier.cpp, and recast in cvc5 style.
 *
 * Not ported: higher-order matching, and the model finder and model checker
 * that implement model based quantifier instantiation. Without the latter,
 * checkModel always answers "unknown", so a quantified problem whose search
 * ends in a satisfying assignment is reported as unknown rather than sat --
 * which is what Z3 itself does when it gives up on the quantifiers.
 */

#include "z3/quantifier_manager.h"

#include <algorithm>
#include <memory>
#include <sstream>
#include <unordered_map>

#include "base/output.h"
#include "z3/ast.h"
#include "z3/enode.h"
#include "z3/mam.h"
#include "z3/qi_queue.h"
#include "z3/smt_context.h"
#include "z3/util/trail.h"

namespace cvc5::internal {
namespace z3 {

QuantifierManagerPlugin* mkDefaultPlugin();

struct QuantifierManager::Imp
{
  QuantifierManager& d_wrapper;
  SmtContext& d_context;
  Params& d_params;
  QiQueue d_qiQueue;
  std::unordered_map<Node, QuantifierStat*> d_quantifierStat;
  std::unordered_map<uint64_t, Node> d_id2Quant;
  QuantifierStatGen d_qstatGen;
  std::vector<Node> d_quantifiers;
  std::unique_ptr<QuantifierManagerPlugin> d_plugin;
  size_t d_numInstances = 0;

  Imp(QuantifierManager& wrapper,
      SmtContext& ctx,
      Params& p,
      QuantifierManagerPlugin* plugin)
      : d_wrapper(wrapper),
        d_context(ctx),
        d_params(p),
        d_qiQueue(wrapper, ctx, p),
        d_qstatGen(ctx.getRegion()),
        d_plugin(plugin)
  {
    d_qiQueue.setup();
  }

  QuantifierStat* getStat(TNode q) const
  {
    auto it = d_quantifierStat.find(q);
    Assert(it != d_quantifierStat.end());
    return it->second;
  }

  uint32_t getGeneration(TNode q) const
  {
    auto it = d_quantifierStat.find(q);
    return it == d_quantifierStat.end() ? 0 : it->second->getGeneration();
  }

  void add(TNode q, uint32_t generation)
  {
    QuantifierStat* stat = d_qstatGen(q, generation);
    d_quantifierStat[q] = stat;
    d_id2Quant[q.getId()] = q;
    d_quantifiers.push_back(q);
    d_plugin->add(q);
  }

  bool hasQuantifiers() const { return !d_quantifiers.empty(); }

  void printStats(std::ostream& out, TNode q)
  {
    QuantifierStat* s = getStat(q);
    uint32_t numInstances = s->getNumInstances();
    uint32_t numInstancesSimplifyTrue = s->getNumInstancesSimplifyTrue();
    uint32_t numInstancesCheckerSat = s->getNumInstancesCheckerSat();
    if (numInstances > 0 || numInstancesSimplifyTrue > 0
        || numInstancesCheckerSat > 0)
    {
      out << "[quantifier_instances] " << getQid(q) << " : " << numInstances
          << " : " << numInstancesSimplifyTrue << " : "
          << numInstancesCheckerSat << " : " << s->getMaxGeneration() << " : "
          << s->getMaxCost() << "\n";
    }
  }

  void del(TNode q)
  {
    if (d_params.d_qiProfile)
    {
      std::stringstream ss;
      printStats(ss, q);
      Warning() << ss.str();
    }
    d_quantifiers.pop_back();
    d_quantifierStat.erase(q);
    d_plugin->del(q);
  }

  bool empty() const { return d_quantifiers.empty(); }

  bool isShared(ENode* n) const { return d_plugin->isShared(n); }

  bool addInstance(TNode q,
                   TNode pat,
                   size_t numBindings,
                   ENode* const* bindings,
                   uint32_t maxGeneration,
                   uint32_t minTopGeneration,
                   uint32_t maxTopGeneration,
                   std::vector<std::pair<ENode*, ENode*>>& /*usedENodes*/)
  {
    if (d_quantifierStat.count(q) == 0)
    {
      return false;
    }

    maxGeneration = std::max(maxGeneration, getGeneration(q));

    getStat(q)->updateMaxGeneration(maxGeneration);
    Fingerprint* f = d_context.addFingerprint(
        q.getId(), static_cast<uint32_t>(q.getId()), numBindings, bindings);
    if (f != nullptr)
    {
      d_qiQueue.insert(
          f, pat, maxGeneration, minTopGeneration, maxTopGeneration);
      d_numInstances++;
    }
    return f != nullptr;
  }

  void initSearchEh()
  {
    d_numInstances = 0;
    for (const Node& q : d_quantifiers)
    {
      getStat(q)->resetNumInstancesCurrSearch();
    }
    d_qiQueue.initSearchEh();
    d_plugin->initSearchEh();
  }

  void assignEh(TNode q) { d_plugin->assignEh(q); }

  void addEqEh(ENode* n1, ENode* n2) { d_plugin->addEqEh(n1, n2); }

  void relevantEh(ENode* n) { d_plugin->relevantEh(n); }

  void restartEh() { d_plugin->restartEh(); }

  void push()
  {
    d_plugin->push();
    d_qiQueue.pushScope();
  }

  void pop(size_t numScopes)
  {
    d_plugin->pop(numScopes);
    d_qiQueue.popScope(numScopes);
  }

  bool canPropagate() const
  {
    return d_qiQueue.hasWork() || d_plugin->canPropagate();
  }

  void propagate()
  {
    d_plugin->propagate();
    d_qiQueue.instantiate();
  }

  FinalCheckStatus finalCheckEh(bool full)
  {
    if (!full)
    {
      return d_plugin->finalCheckEh(false);
    }
    FinalCheckStatus result = d_qiQueue.finalCheckEh() ? FC_DONE : FC_CONTINUE;
    FinalCheckStatus presult = d_plugin->finalCheckEh(full);
    if (presult != FC_DONE)
    {
      result = presult;
    }
    if (d_context.canPropagate())
    {
      result = FC_CONTINUE;
    }
    return result;
  }

  CheckModelResult checkModel()
  {
    if (empty())
    {
      return SAT;
    }
    return d_plugin->checkModel();
  }
};

QuantifierManager::QuantifierManager(SmtContext& ctx, Params& fp)
    : d_lazyScopes(0), d_lazy(true)
{
  d_imp.reset(new Imp(*this, ctx, fp, mkDefaultPlugin()));
  d_imp->d_plugin->setManager(*this);
}

QuantifierManager::~QuantifierManager() {}

SmtContext& QuantifierManager::getContext() const { return d_imp->d_context; }

void QuantifierManager::add(TNode q, uint32_t generation)
{
  if (d_lazy)
  {
    // The plugin's scopes are only created once the first quantifier shows
    // up, so that a problem without quantifiers pays nothing.
    while (d_lazyScopes > 0)
    {
      --d_lazyScopes;
      d_imp->push();
    }
    d_lazy = false;
  }
  d_imp->add(q, generation);
}

void QuantifierManager::del(TNode q) { d_imp->del(q); }

bool QuantifierManager::empty() const { return d_imp->empty(); }

bool QuantifierManager::isShared(ENode* n) const { return d_imp->isShared(n); }

QuantifierStat* QuantifierManager::getStat(TNode q) const
{
  return d_imp->getStat(q);
}

TNode QuantifierManager::getQuantifierById(uint64_t id) const
{
  auto it = d_imp->d_id2Quant.find(id);
  Assert(it != d_imp->d_id2Quant.end());
  return it->second;
}

uint32_t QuantifierManager::getGeneration(TNode q) const
{
  return d_imp->getGeneration(q);
}

bool QuantifierManager::addInstance(
    TNode q,
    TNode pat,
    size_t numBindings,
    ENode* const* bindings,
    uint32_t maxGeneration,
    uint32_t minTopGeneration,
    uint32_t maxTopGeneration,
    std::vector<std::pair<ENode*, ENode*>>& usedENodes)
{
  return d_imp->addInstance(q,
                            pat,
                            numBindings,
                            bindings,
                            maxGeneration,
                            minTopGeneration,
                            maxTopGeneration,
                            usedENodes);
}

bool QuantifierManager::addInstance(TNode q,
                                    size_t numBindings,
                                    ENode* const* bindings,
                                    uint32_t generation)
{
  std::vector<std::pair<ENode*, ENode*>> tmp;
  return addInstance(q,
                     TNode::null(),
                     numBindings,
                     bindings,
                     generation,
                     generation,
                     generation,
                     tmp);
}

void QuantifierManager::initSearchEh() { d_imp->initSearchEh(); }

void QuantifierManager::assignEh(TNode q) { d_imp->assignEh(q); }

void QuantifierManager::addEqEh(ENode* n1, ENode* n2)
{
  d_imp->addEqEh(n1, n2);
}

void QuantifierManager::relevantEh(ENode* n) { d_imp->relevantEh(n); }

FinalCheckStatus QuantifierManager::finalCheckEh(bool full)
{
  return d_imp->finalCheckEh(full);
}

void QuantifierManager::restartEh() { d_imp->restartEh(); }

bool QuantifierManager::canPropagate() const { return d_imp->canPropagate(); }

void QuantifierManager::propagate() { d_imp->propagate(); }

bool QuantifierManager::modelBased() const
{
  return d_imp->d_plugin->modelBased();
}

bool QuantifierManager::hasQuantifiers() const
{
  return d_imp->hasQuantifiers();
}

bool QuantifierManager::mbqiEnabled(TNode q) const
{
  return d_imp->d_plugin->mbqiEnabled(q);
}

QuantifierManager::CheckModelResult QuantifierManager::checkModel()
{
  return d_imp->checkModel();
}

void QuantifierManager::push()
{
  if (d_lazy)
  {
    ++d_lazyScopes;
  }
  else
  {
    d_imp->push();
  }
}

void QuantifierManager::pop(size_t numScopes)
{
  if (d_lazy)
  {
    d_lazyScopes -= numScopes;
  }
  else
  {
    d_imp->pop(numScopes);
  }
}

void QuantifierManager::reset() {}

void QuantifierManager::print(std::ostream& /*out*/) const {}

const std::vector<Node>& QuantifierManager::quantifiers() const
{
  return d_imp->d_quantifiers;
}

size_t QuantifierManager::numQuantifiers() const
{
  return d_imp->d_quantifiers.size();
}

namespace {

/** The default strategy: E-matching, as in Z3. */
class DefaultQmPlugin : public QuantifierManagerPlugin
{
 public:
  DefaultQmPlugin()
      : d_qm(nullptr),
        d_params(nullptr),
        d_context(nullptr),
        d_newENodeQhead(0),
        d_lazyMatchingIdx(0),
        d_active(false)
  {
  }

  void setManager(QuantifierManager& qm) override
  {
    Assert(d_qm == nullptr);
    d_qm = &qm;
    d_context = &(qm.getContext());
    d_params = &(d_context->getParams());

    d_mam.reset(mkMam(*d_context));
    d_lazyMam.reset(mkMam(*d_context));
  }

  bool modelBased() const override { return d_params->d_mbqi; }

  bool mbqiEnabled(TNode /*q*/) const override { return true; }

  void add(TNode q) override
  {
    if (d_params->d_mbqi && mbqiEnabled(q))
    {
      d_active = true;
    }
  }

  void del(TNode /*q*/) override {}

  void push() override
  {
    d_mam->pushScope();
    d_lazyMam->pushScope();
  }

  void pop(size_t numScopes) override
  {
    d_mam->popScope(numScopes);
    d_lazyMam->popScope(numScopes);
  }

  void initSearchEh() override { d_lazyMatchingIdx = 0; }

  void assignEh(TNode q) override
  {
    d_active = true;
    if (!d_params->d_ematching)
    {
      return;
    }
    // A multi-pattern is only matched eagerly up to a bound, since matching
    // one is much more expensive than matching a unary pattern. The bound is
    // raised by one when the quantifier has no unary pattern at all, so that
    // at least one of its patterns is always matched eagerly.
    std::vector<std::vector<Node>> patterns;
    getPatterns(q, patterns);
    bool hasUnaryPattern = false;
    for (const std::vector<Node>& mp : patterns)
    {
      if (mp.size() == 1)
      {
        hasUnaryPattern = true;
        break;
      }
    }
    uint32_t numEagerMultiPatterns = d_params->d_qiMaxEagerMultipatterns;
    if (!hasUnaryPattern)
    {
      numEagerMultiPatterns++;
    }
    TNode ipl = q.getNumChildren() == 3 ? q[2] : TNode::null();
    size_t j = 0;
    if (!ipl.isNull())
    {
      for (const Node& mp : ipl)
      {
        if (mp.getKind() != Kind::INST_PATTERN)
        {
          continue;
        }
        bool unary = mp.getNumChildren() == 1;
        if (!unary && j >= numEagerMultiPatterns)
        {
          d_lazyMam->addPattern(q, mp);
        }
        else
        {
          d_mam->addPattern(q, mp);
        }
        if (!unary)
        {
          j++;
        }
      }
    }
  }

  bool useEmatching() const { return d_params->d_ematching && !d_qm->empty(); }

  void addEqEh(ENode* e1, ENode* e2) override
  {
    if (useEmatching())
    {
      d_mam->addEqEh(e1, e2);
    }
  }

  void relevantEh(ENode* e) override
  {
    if (useEmatching())
    {
      d_mam->relevantEh(e, false);
      d_lazyMam->relevantEh(e, true);
    }
  }

  bool canPropagate() const override { return d_active && d_mam->hasWork(); }

  void restartEh() override {}

  bool isShared(ENode* n) const override
  {
    return d_active && (d_mam->isShared(n) || d_lazyMam->isShared(n));
  }

  void propagate() override
  {
    if (!d_active)
    {
      return;
    }
    d_mam->match();
    if (!d_context->relevancy() && useEmatching())
    {
      // Without relevancy every new enode is a matching candidate, so the
      // code trees are fed directly from the enode list.
      const ENodeVector& enodes = d_context->enodes();
      size_t sz = enodes.size();
      if (sz > d_newENodeQhead)
      {
        d_context->pushTrail(ValueTrail<size_t>(d_newENodeQhead));
        while (d_newENodeQhead < sz)
        {
          ENode* e = enodes[d_newENodeQhead];
          d_mam->relevantEh(e, false);
          d_lazyMam->relevantEh(e, true);
          d_newENodeQhead++;
        }
      }
    }
  }

  QuantifierManager::CheckModelResult checkModel() override
  {
    // Model based quantifier instantiation is not ported, so the search
    // cannot confirm that the candidate model satisfies the quantifiers.
    return QuantifierManager::UNKNOWN;
  }

  FinalCheckStatus finalCheckEh(bool full) override
  {
    if (!full)
    {
      if (d_params->d_qiLazyInstantiation)
      {
        return finalCheckQuant();
      }
      return FC_DONE;
    }
    return finalCheckQuant();
  }

 private:
  FinalCheckStatus finalCheckQuant()
  {
    if (useEmatching())
    {
      if (d_lazyMatchingIdx < d_params->d_qiMaxLazyMultipatternMatching)
      {
        d_lazyMam->rematch();
        d_context->pushTrail(ValueTrail<size_t>(d_lazyMatchingIdx));
        d_lazyMatchingIdx++;
      }
    }
    return FC_DONE;
  }

  QuantifierManager* d_qm;
  Params* d_params;
  SmtContext* d_context;
  std::unique_ptr<Mam> d_mam;
  std::unique_ptr<Mam> d_lazyMam;
  size_t d_newENodeQhead;
  size_t d_lazyMatchingIdx;
  bool d_active;
};

}  // namespace

QuantifierManagerPlugin* mkDefaultPlugin() { return new DefaultQmPlugin(); }

}  // namespace z3
}  // namespace cvc5::internal
