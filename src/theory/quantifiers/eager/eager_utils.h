/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Eager instantiation.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__EAGER_UTILS_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__EAGER_UTILS_H

#include "context/cdhashset.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/eager/eager_ground_trie.h"
#include "theory/quantifiers/eager/eager_trie.h"
#include "theory/quantifiers/quant_module.h"
#include "util/hash.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

using EagerWatchVec = std::vector<std::pair<const EagerTrie*, TNode>>;
using EagerWatchSet = std::map<TNode, std::unordered_set<TNode>>;
using EagerGtMVector = std::vector<std::vector<EagerGroundTrie*>>;
using EagerFailExp =
    std::map<TNode, std::map<TNode, std::pair<EagerWatchVec, EagerWatchVec>>>;

class EagerWatchList
{
  using WatchJob = std::pair<const EagerTrie*, Node>;
  using WatchJobHash = PairHashFunction<const EagerTrie*,
                                        Node,
                                        std::hash<const EagerTrie*>,
                                        std::hash<Node>>;

 public:
  EagerWatchList(context::Context* c)
      : d_valid(c, true), d_matchJobs(c), d_matchJobSet(c)
  {
  }
  void add(const EagerTrie* et, TNode t);
  void addMatchJobs(EagerWatchList* ewl);
  context::CDO<bool> d_valid;
  context::CDList<std::pair<const EagerTrie*, TNode>> d_matchJobs;
  context::CDHashSet<WatchJob, WatchJobHash> d_matchJobSet;
};

class EagerRepInfo
{
 public:
  EagerRepInfo(context::Context* c) : d_eqWatch(c), d_opWatch(c), d_ctx(c) {}
  EagerWatchList* getOrMkListForRep(const Node& r, bool doMk);
  EagerWatchList* getOrMkListForOp(const Node& r, bool doMk);
  /**
   * Mapping from terms in the above list to the term we are waiting the
   * equivalence class to become equal to.
   */
  context::CDHashMap<Node, std::shared_ptr<EagerWatchList>> d_eqWatch;
  /**
   * Map from operators to a witness term and a watch list.
   * If an f-term is added to this equivalence class, we set it as the first
   * part of this pair and reprocess the watch list that is the second part of
   * the pair.
   */
  context::CDHashMap<Node, std::pair<Node, std::shared_ptr<EagerWatchList>>>
      d_opWatch;

 private:
  context::Context* d_ctx;
};

// TODO: for preregister
/*
class EagerQuantInfo
{
 public:
  EagerQuantInfo(context::Context* c) : d_ewl(c) {}
  context::CDList<std::pair<const EagerTrie*, TNode>> d_matchJobs;
};
*/

class EagerOpInfo
{
 public:
  EagerOpInfo(context::Context* c, const Node& op, EagerGroundDb* gdb);
  /** Add ground term */
  bool addGroundTerm(QuantifiersState& qs, const Node& n);
  /** Get ground terms */
  const context::CDHashSet<Node>& getGroundTerms(QuantifiersState& qs);
  /** */
  CDEagerTrie* getPatternTrie() { return &d_etrie; }
  /**
   * Mark that we are tracking terms of this operator, for non-simple matching.
   */
  void markWatchOp();
  /** */
  bool isWatchOp() const { return d_isWatchOp; }

 private:
  /** Add ground term */
  bool addGroundTermInternal(QuantifiersState& qs, const Node& n);
  /** For ground term indexing */
  EagerGroundTrieAllocator* d_galloc;
  EagerGroundTrie* d_gtrie;
  /** Relevant terms for this in the current context */
  context::CDHashSet<Node> d_rlvTerms;
  /** Relevant terms for this in the current context */
  context::CDHashSet<Node> d_rlvTermsWaiting;
  /** */
  context::CDO<bool> d_active;
  /** */
  CDEagerTrie d_etrie;
  /** Are we watching this operator? */
  bool d_isWatchOp;
};

class EagerPatternInfo
{
 public:
  EagerPatternInfo(context::Context* c, const Node& q)
      : d_quant(q), d_pmatches(c)
  {
  }
  void addMultiTriggerContext(const Node& pat, size_t i)
  {
    d_multiCtx.emplace_back(pat, i);
  }
  /** */
  const Node& getQuantFormula() const { return d_quant; }
  const std::vector<std::pair<Node, size_t>>& getMultiCtx() const
  {
    return d_multiCtx;
  }
  EagerGroundTrie* getPartialMatches() { return &d_pmatches; }

 private:
  Node d_quant;
  std::vector<std::pair<Node, size_t>> d_multiCtx;
  EagerGroundTrie d_pmatches;
};

class EagerMultiPatternInfo
{
 public:
  EagerMultiPatternInfo() {}
  /** The list of eager pattern infos */
  std::vector<EagerPatternInfo*> d_epis;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
