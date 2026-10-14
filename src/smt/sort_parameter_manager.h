/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved. See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************/

#include "cvc5_private.h"
#ifndef CVC5__SMT__SORT_PARAMETER_MANAGER_H
#define CVC5__SMT__SORT_PARAMETER_MANAGER_H

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
class LazyCDProof;
namespace preprocessing {
class AssertionPipeline;
}
namespace smt {
class Assertions;

/** Instantiate schematic assertions over the current sort signature. */
class SortParameterManager : protected EnvObj
{
 public:
  SortParameterManager(Env& env);
  ~SortParameterManager();
  /** Register a sort declaration in the current user scope. */
  void declareSort(TypeNode type);
  /** Move pre-initialization declarations into the initial assertion scope. */
  void finishInit();
  /** Add any new instances, including instances of earlier assertions. */
  void instantiate(Assertions& assertions,
                   preprocessing::AssertionPipeline& pipeline);
  /** Whether all sort instances of the active assertions have been checked. */
  bool isComplete() const { return d_complete; }
  /** Ground instances, for model checking. */
  const context::CDList<Node>& getInstances() const { return d_instances; }
  /** The finite part of the current ground signature. */
  const std::vector<TypeNode>& getGroundSorts() const { return d_groundSorts; }

 private:
  context::CDList<TypeNode> d_declarations;
  std::vector<TypeNode> d_globalDeclarations;
  std::vector<TypeNode> d_pendingDeclarations;
  context::CDHashSet<Node> d_processed;
  context::CDList<Node> d_instances;
  std::unique_ptr<LazyCDProof> d_proof;
  std::vector<TypeNode> d_groundSorts;
  bool d_complete = true;
};
}  // namespace smt
}  // namespace cvc5::internal
#endif
