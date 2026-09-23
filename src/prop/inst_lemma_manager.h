/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Instantiation lemma manager.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__INST_LEMMA_MANAGER_H
#define CVC5__PROP__INST_LEMMA_MANAGER_H

#include <memory>
#include <vector>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace prop {

/**
 * This class manages the mapping between quantified formulas and the
 * instantiation lemmas that were generated for them.
 *
 * An instantiation lemma (=> q body) for quantified formula q is added to the
 * decision engine as an ordinary (user-context) assertion. However, the
 * decision engine only attempts to satisfy it (i.e. make its body relevant)
 * when q is asserted. This class records the association q -> lemmas, and is
 * used to prompt the decision engine to revisit the lemmas of q when q becomes
 * asserted (which is necessary when q is asserted after the decision engine has
 * already iterated past the lemma in the current SAT context).
 *
 * It tracks (in a SAT-context-dependent manner) which quantified formulas are
 * "active", i.e. have been asserted in the current SAT context, so that the
 * revisit notification is sent at most once per activation of q.
 */
class InstLemmaManager
{
  using NodeList = context::CDList<Node>;
  using NodeListMap = context::CDHashMap<Node, std::shared_ptr<NodeList>>;
  using NodeSet = context::CDHashSet<Node>;

 public:
  InstLemmaManager(context::Context* context,
                   context::UserContext* userContext);
  ~InstLemmaManager();

  /**
   * Notify that lem is an instantiation lemma associated with quantified
   * formula q. This records the association q -> lem.
   *
   * @param q The quantified formula the lemma was generated for
   * @param lem The instantiation lemma
   */
  void notifyInstLemma(TNode q, Node lem);

  /**
   * Notify that the given literal has been asserted. If literal is a quantified
   * formula that has not yet been marked active in the current SAT context,
   * it is marked active and all of its recorded instantiation lemmas are added
   * to revisitLemmas, so that the decision engine can be prompted to revisit
   * them.
   *
   * @param literal The literal that became asserted
   * @param revisitLemmas The list to add the instantiation lemmas of literal to
   */
  void notifyAsserted(TNode literal, std::vector<TNode>& revisitLemmas);

 private:
  /** Get (or make) the lemma list for quantified formula q */
  NodeList* getOrMkList(TNode q);
  /** The user context */
  context::UserContext* d_userContext;
  /** quantified formulas to their instantiation lemmas (user-context) */
  NodeListMap d_qlemmas;
  /** set of active (asserted) quantified formulas (SAT-context) */
  NodeSet d_qactive;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__PROP__INST_LEMMA_MANAGER_H */
