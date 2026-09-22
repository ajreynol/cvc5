/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The lazy propositional engine
 */

#include "prop/lazy_prop_engine.h"

#include "prop/prop_engine.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"

namespace cvc5::internal {
namespace prop {

LazyPropEngine::LazyPropEngine(Env& env, TheoryEngine* te, PropEngine* pe)
    : EnvObj(env), d_theoryEngine(te), d_propEngine(pe)
{
}

Result LazyPropEngine::checkSat(
    const context::CDList<Node>& assertions,
    const context::CDHashMap<size_t, Node>& skolemMap)
{
  Trace("lazy-prop") << "lazy check-sat, #assertions=" << assertions.size()
                     << std::endl;
  // By default, we do:
  //   d_propEngine->assertInputFormulas(assertions, skolemMap);
  //   d_propEngine->checkSat();
  // Instead, this method pushes assertions to the prop engine one at a time
  // based on the model for the current set.

  size_t indexCheck = 0;
  size_t asize = assertions.size();
  Result r;
  std::unordered_set<size_t> assertionsAdded;
  context::CDHashMap<size_t, Node>::const_iterator itk;
  while (true)
  {
    // check sat with the current assertions
    r = d_propEngine->checkSat();
    Trace("lazy-prop") << "...check-sat " << r << std::endl;
    // if we've added all assertions, or we are unsat, we are done
    if (assertionsAdded.size() == asize || r.getStatus() == Result::UNSAT)
    {
      break;
    }
    theory::TheoryModel* tm = d_theoryEngine->getBuiltModel();
    // otherwise, get an arbitrary assertion that is not satisfied
    bool bestIndexSet = false;
    size_t bestIndex = 0;
    size_t indexCheckEnd = indexCheck;
    do
    {
      if (assertionsAdded.find(indexCheck) == assertionsAdded.end())
      {
        Node val = tm->getValue(assertions[indexCheck]);
        if (val.isConst())
        {
          if (!val.getConst<bool>())
          {
            // assertion is false, add it now
            bestIndexSet = true;
            bestIndex = indexCheck;
            Trace("lazy-prop") << "...found falsified" << std::endl;
            break;
          }
        }
        else if (!bestIndexSet)
        {
          // assertion is unknown, keep it unless we find a better one
          bestIndexSet = true;
          bestIndex = indexCheck;
        }
      }
      // increment the index
      indexCheck = (indexCheck + 1 == asize ? 0 : indexCheck + 1);
    } while (indexCheck != indexCheckEnd);

    if (!bestIndexSet && r.getStatus() == Result::SAT)
    {
      // current model satisfies all remaining assertions
      break;
    }
    Trace("lazy-prop") << "...add assertion #" << bestIndex << ", now " << assertionsAdded.size() << "/" << asize << " assertions added" << std::endl;
    // add the best index
    assertionsAdded.insert(bestIndex);
    // add the single assertion
    std::vector<Node> newAssertion = {assertions[bestIndex]};
    // check if the new assertion is associated with a skolem
    std::unordered_map<size_t, Node> newSkolemMap;
    itk = skolemMap.find(bestIndex);
    if (itk != skolemMap.end())
    {
      newSkolemMap[0] = itk->second;
    }
    Trace("lazy-prop-debug") << "(assert " << newAssertion[0] << ")" << std::endl;
    d_propEngine->resetTrail();
    d_propEngine->assertInputFormulas(newAssertion, newSkolemMap);
  }
  Trace("lazy-prop") << "...finish " << r << " with " << assertionsAdded.size()
                     << "/" << asize << " added assertions" << std::endl;
  return r;
}

}  // namespace prop
}  // namespace cvc5::internal
