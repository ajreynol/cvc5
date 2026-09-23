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
 * Term manager.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__TERM_MANAGER__H
#define CVC5__THEORY__TERM_MANAGER__H

#include <unordered_map>
#include <unordered_set>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "expr/node.h"
#include "theory/theory_engine_module.h"

namespace cvc5::internal {
namespace theory {

/**
 */
class TermDbManager : public TheoryEngineModule
{
 public:
  /**
   * @param env The environment
   * @param engine The parent theory engine
   */
  TermDbManager(Env& env, TheoryEngine* engine);
  /**
   * Notify (preprocessed) assertions.
   * @param assertions The assertions
   */
  void notifyPreprocessedAssertions(const std::vector<Node>& assertions);
  /** Notify lemma */
  void notifyLemma(TNode n,
                   InferenceId id,
                   LemmaProperty p,
                   const std::vector<Node>& skAsserts,
                   const std::vector<Node>& sks) override;
  /** Can we instantiation q with term n based on its origin information? */
  bool canInstantiate(const Node& q, const Node& n);

 private:
  class TermOrigin
  {
   public:
    TermOrigin(context::Context* c, const Node& t);
    /** */
    int64_t getQuantifierDepth(const Node& q) const;
    /** This term */
    Node d_this;
    /**
     * Edges to children, labelled with the quantified formulas that were
     * used to generate the child term.
     */
    context::CDHashMap<TermOrigin*, std::vector<Node>> d_children;
    /**
     * Set of parent terms
     */
    context::CDHashSet<TermOrigin*> d_parents;
    /**
     * The nested depth of this term, for each relevant quantified formula.
     * Quantified formulas that are not present are 0. This is the minimial
     * number of times the quantified formula occurs on a label in a path
     * from this term to an input term.
     *
     * This map is incrementally maintained as d_children/d_parents is updated.
     */
    context::CDHashMap<Node, int64_t> d_quantDepth;
  };
  /** Mapping */
  context::CDHashMap<Node, std::shared_ptr<TermOrigin>> d_omap;
  /** Mapping quantified formulas to their explicitly given inst nested level */
  context::CDHashMap<Node, int64_t> d_qinLevel;
  /** The input terms */
  context::CDHashSet<Node> d_inputTerms;
  /**
   */
  int64_t getInstNestedMaxLimit(const Node& q) const;
  /**
   */
  TermOrigin* getOrMkTermOrigin(const Node& t);
  /**
   * If id is InferenceId::NONE, the term was from the input formulas.
   * If args is provided, it is of the form (Q t_1 ... t_n),
   * where quantified formula Q was instantiated with t_1 ... t_n to generate
   * n.
   * @param n The term we saw in an input formula or lemma.
   * @param id The identifier indicating the lemma (if applicable) that
   * generated this term.
   * @param args The arguments.
   */
  void addOrigin(const Node& n,
                 InferenceId id,
                 const Node& q,
                 const std::vector<TermOrigin*>& args);
  /**
   * Do any term-specific initialization, called once when the term n is first
   * seen in the user context.
   */
  void initializeTerm(const Node& n);
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__RELEVANCE_MANAGER__H */
