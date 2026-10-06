/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Evaluator for regular expression membership.
 */

#include "theory/strings/regexp_eval.h"

#include <algorithm>
#include <cstdint>

#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "util/regexp.h"
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

/**
 * An NFA state.
 *
 * Edges can be annotated with constant characters, re.allchar or re.range
 * regular expressions.
 *
 * Regular expressions can be compiled to an NFA via construct. Evaluation
 * is computed via addToNext and processNextChar.
 */
class NfaState
{
 public:
  /**
   * Returns the NFA for regular expression r, connects the dangling arrows
   * to the given accept state.
   */
  static NfaState* construct(Node r,
                             NfaState* accept,
                             std::vector<std::shared_ptr<NfaState>>& scache)
  {
    NfaState* rs = constructInternal(r, scache);
    rs->connectTo(accept);
    return rs;
  }
  /**
   * Adds this state and all children connected by null to next.
   */
  void addToNext(std::unordered_set<NfaState*>& next)
  {
    // have property that all child states are also added to next if this
    // state has been added to next
    if (next.find(this) != next.end())
    {
      return;
    }
    next.insert(this);
    std::map<Node, std::vector<NfaState*>>::iterator it =
        d_children.find(Node::null());
    if (it != d_children.end())
    {
      for (NfaState* cs : it->second)
      {
        cs->addToNext(next);
      }
    }
  }
  /**
   * Processes the next input character nextChar from this state. Adds all
   * next states to process to the next set.
   */
  void processNextChar(unsigned nextChar, std::unordered_set<NfaState*>& next)
  {
    for (const std::pair<const Node, std::vector<NfaState*>>& c : d_children)
    {
      const Node& r = c.first;
      if (r.isNull())
      {
        continue;
      }
      bool accepts = false;
      switch (r.getKind())
      {
        case Kind::CONST_STRING:
          Assert(r.getConst<String>().size() == 1);
          accepts = (nextChar == r.getConst<String>().front());
          break;
        case Kind::REGEXP_RANGE:
        {
          unsigned a = r[0].getConst<String>().front();
          unsigned b = r[1].getConst<String>().front();
          accepts = (a <= nextChar && nextChar <= b);
        }
        break;
        case Kind::REGEXP_ALLCHAR: accepts = true; break;
        default: Unreachable() << "Unknown NFA edge " << c.first; break;
      }
      if (accepts)
      {
        for (NfaState* cs : c.second)
        {
          cs->addToNext(next);
        }
      }
    }
  }

 private:
  /**
   * Returns the (partial) NFA for regular expression r, whose dangling arrows
   * are in d_arrows of the returned NfaState.
   */
  static NfaState* constructInternal(
      Node r, std::vector<std::shared_ptr<NfaState>>& scache)
  {
    Kind k = r.getKind();
    // Concatenation does not introduce a new state, instead returns the
    // state of the first child.
    if (k == Kind::REGEXP_CONCAT)
    {
      NfaState* first = nullptr;
      NfaState* curr = nullptr;
      for (const Node& rc : r)
      {
        NfaState* rcs = constructInternal(rc, scache);
        if (first == nullptr)
        {
          first = rcs;
          curr = first;
          continue;
        }
        // connect previous to next
        curr->connectTo(rcs);
        // update current
        curr = rcs;
      }
      // should have had 2+ arguments
      Assert(curr != first && curr != nullptr && first != nullptr);
      // copy arrows from last to first
      first->d_arrows = curr->d_arrows;
      curr->d_arrows.clear();
      return first;
    }
    // Otherwise allocate a state.
    NfaState* s = allocateState(scache);
    std::vector<std::pair<NfaState*, Node>>& sarrows = s->d_arrows;
    switch (k)
    {
      case Kind::STRING_TO_REGEXP:
      {
        Assert(r[0].isConst());
        const String& str = r[0].getConst<String>();
        if (str.size() == 0)
        {
          // The regular expression is a no-op.
          sarrows.emplace_back(s, Node::null());
        }
        else
        {
          // this constructs N states in concatenation, where N is the length of
          // the string, each connected via single characters
          const std::vector<unsigned>& vec = str.getVec();
          NfaState* curr = s;
          NodeManager* nm = r.getNodeManager();
          for (size_t i = 0, nvec = vec.size(); i < nvec; i++)
          {
            std::vector<unsigned> charVec{vec[i]};
            Node nextChar = nm->mkConst(String(charVec));
            if (i + 1 == vec.size())
            {
              // the last edge is the dangling pointer of the first
              sarrows.emplace_back(curr, nextChar);
            }
            else
            {
              NfaState* next = allocateState(scache);
              curr->d_children[nextChar].push_back(next);
              curr = next;
            }
          }
        }
      }
      break;
      case Kind::REGEXP_ALLCHAR:
      case Kind::REGEXP_RANGE: sarrows.emplace_back(s, r); break;
      case Kind::REGEXP_UNION:
      {
        // connect to all children via null, take union of arrows
        std::vector<NfaState*>& schildren = s->d_children[Node::null()];
        for (const Node& rc : r)
        {
          NfaState* rcs = constructInternal(rc, scache);
          schildren.push_back(rcs);
          std::vector<std::pair<NfaState*, Node>>& rcsarrows = rcs->d_arrows;
          sarrows.insert(sarrows.end(), rcsarrows.begin(), rcsarrows.end());
          rcsarrows.clear();
        }
      }
      break;
      case Kind::REGEXP_STAR:
      {
        NfaState* body = constructInternal(r[0], scache);
        s->d_children[Node::null()].push_back(body);
        // body loops back to this state
        body->connectTo(s);
        // skip moves on
        sarrows.emplace_back(s, Node::null());
      }
      break;
      case Kind::REGEXP_LOOP:
      {
        // ((_ re.loop l u) R) is unrolled to the concatenation of l copies of
        // R followed by u-l copies of R that may be skipped. Note that u >= 1
        // here, since otherwise the term would have been rewritten.
        uint32_t l = utils::getLoopMinOccurrences(r);
        uint32_t u = utils::getLoopMaxOccurrences(r);
        if (u < l)
        {
          // the language is empty, s is a dead end with no exit arrows
          break;
        }
        NfaState* curr = s;
        for (uint32_t i = 0; i < u; i++)
        {
          NfaState* body = constructInternal(r[0], scache);
          if (i < l)
          {
            // a mandatory copy, which we must traverse
            curr->d_children[Node::null()].push_back(body);
          }
          else
          {
            // An optional copy. We introduce a state that either moves to the
            // body or skips to the end of the loop.
            NfaState* opt = allocateState(scache);
            curr->d_children[Node::null()].push_back(opt);
            opt->d_children[Node::null()].push_back(body);
            // skipping the remaining copies moves past the loop
            sarrows.emplace_back(opt, Node::null());
          }
          // the dangling arrows of the body are the dangling arrows of the
          // next iteration
          NfaState* next = allocateState(scache);
          body->connectTo(next);
          curr = next;
        }
        sarrows.emplace_back(curr, Node::null());
      }
      break;
      default: Unreachable() << "Unknown regular expression " << r; break;
    }
    return s;
  }
  /** Connect dangling arrows of this to state s and clear */
  void connectTo(NfaState* s)
  {
    for (std::pair<NfaState*, Node>& a : d_arrows)
    {
      a.first->d_children[a.second].push_back(s);
    }
    d_arrows.clear();
  }
  /** Allocate state, add to cache (for memory management) */
  static NfaState* allocateState(std::vector<std::shared_ptr<NfaState>>& scache)
  {
    std::shared_ptr<NfaState> ret = std::make_shared<NfaState>();
    scache.push_back(ret);
    return ret.get();
  }
  /**
   * Edges from this state. Maps constant characters, re.allchar or re.range
   * to the list of children connected via an edge with that label.
   */
  std::map<Node, std::vector<NfaState*>> d_children;
  /** Current dangling pointers */
  std::vector<std::pair<NfaState*, Node>> d_arrows;
};

/**
 * The maximum number of NFA states we are willing to construct for a re.loop
 * term in NfaState::construct below. Note that re.loop is the only operator
 * that may require a number of states that is not linear in the size of the
 * regular expression, since its body is duplicated once per iteration.
 */
static constexpr uint64_t s_nfaLoopStateLimit = 100000;

/**
 * Accumulates into size an upper bound on the number of states that
 * NfaState::construct requires for r. Returns false if r contains an operator
 * that we cannot compile to an NFA, or if size exceeds s_nfaLoopStateLimit.
 *
 * Note that states are not shared between multiple occurrences of the same
 * subterm, hence this is computed as a traversal of the term tree. Since we
 * abort as soon as the bound is exceeded, this takes time linear in
 * s_nfaLoopStateLimit.
 */
static bool computeNfaSize(TNode r, uint64_t& size)
{
  switch (r.getKind())
  {
    case Kind::STRING_TO_REGEXP:
      if (!r[0].isConst())
      {
        return false;
      }
      size += std::max(static_cast<uint64_t>(Word::getLength(r[0])),
                       static_cast<uint64_t>(1));
      break;
    case Kind::REGEXP_RANGE:
      if (!utils::isCharacterRange(r))
      {
        return false;
      }
      size += 1;
      break;
    case Kind::REGEXP_ALLCHAR: size += 1; break;
    case Kind::REGEXP_CONCAT:
    case Kind::REGEXP_UNION:
    case Kind::REGEXP_STAR:
      size += 1;
      for (const Node& rc : r)
      {
        if (!computeNfaSize(rc, size))
        {
          return false;
        }
      }
      break;
    case Kind::REGEXP_LOOP:
    {
      uint32_t l = utils::getLoopMinOccurrences(r);
      uint32_t u = utils::getLoopMaxOccurrences(r);
      if (u < l)
      {
        // the language is empty, which requires a single dead end state
        size += 1;
        break;
      }
      // the body is duplicated u times, with two additional states per copy
      uint64_t bodySize = 0;
      if (!computeNfaSize(r[0], bodySize))
      {
        return false;
      }
      size += 1 + static_cast<uint64_t>(u) * (bodySize + 2);
    }
    break;
    default: return false;
  }
  return (size <= s_nfaLoopStateLimit);
}

bool RegExpEval::canEvaluate(const Node& r)
{
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(r);
  do
  {
    cur = visit.back();
    visit.pop_back();
    // if not already visited
    if (visited.insert(cur).second)
    {
      switch (cur.getKind())
      {
        case Kind::STRING_TO_REGEXP:
          if (!cur[0].isConst())
          {
            return false;
          }
          break;
        case Kind::REGEXP_RANGE:
          if (!utils::isCharacterRange(cur))
          {
            return false;
          }
          break;
        case Kind::REGEXP_ALLCHAR: break;
        case Kind::REGEXP_UNION:
        case Kind::REGEXP_CONCAT:
        case Kind::REGEXP_STAR:
          for (const Node& cc : cur)
          {
            visit.push_back(cc);
          }
          break;
        case Kind::REGEXP_LOOP:
        {
          // Unrolling the loop duplicates its body, so we additionally ensure
          // that the resulting NFA is not too large. Note this also checks
          // that the body can be compiled to an NFA, hence we do not traverse
          // into it below.
          uint64_t size = 0;
          if (!computeNfaSize(cur, size))
          {
            return false;
          }
        }
        break;
        default: return false;
      }
    }
  } while (!visit.empty());
  return true;
}

bool RegExpEval::evaluate(String& s, const Node& r)
{
  Trace("re-eval") << "Evaluate " << s << " in " << r << std::endl;
  // no intersection, complement, and r must be constant.
  Assert(canEvaluate(r));
  NfaState accept;
  std::vector<std::shared_ptr<NfaState>> scache;
  NfaState* rs = NfaState::construct(r, &accept, scache);
  Trace("re-eval") << "NFA size is " << (scache.size() + 1) << std::endl;
  std::unordered_set<NfaState*> curr;
  rs->addToNext(curr);
  const std::vector<unsigned>& vec = s.getVec();
  for (size_t i = 0, nvec = vec.size(); i < nvec; i++)
  {
    Trace("re-eval") << "..process next char " << vec[i]
                     << ", #states=" << curr.size() << std::endl;
    std::unordered_set<NfaState*> next;
    for (NfaState* cs : curr)
    {
      cs->processNextChar(vec[i], next);
    }
    // if there are no more states, we are done
    if (next.empty())
    {
      return false;
    }
    curr = next;
  }
  Trace("re-eval") << "..finish #states=" << curr.size() << std::endl;
  return curr.find(&accept) != curr.end();
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
