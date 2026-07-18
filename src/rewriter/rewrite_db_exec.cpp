/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Executable (interpreted) rewrite trie.
 */

#include "rewriter/rewrite_db_exec.h"

#include <algorithm>

#include "expr/nary_term_util.h"
#include "expr/node_manager.h"
#include "rewriter/rewrites.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace rewriter {

void RewriteExecTrie::addTerm(const Node& n, size_t ruleIndex)
{
  Assert(!n.isNull());
  std::vector<Node> visit{n};
  RewriteExecTrie* curr = this;
  while (!visit.empty())
  {
    Node cn = visit.back();
    visit.pop_back();
    if (cn.hasOperator())
    {
      curr = &(curr->d_children[cn.getOperator()][cn.getNumChildren()]);
      // children are processed as a stack (right-to-left), matching getMatch
      for (const Node& cnc : cn)
      {
        visit.push_back(cnc);
      }
    }
    else
    {
      if (cn.isVar()
          && std::find(curr->d_vars.begin(), curr->d_vars.end(), cn)
                 == curr->d_vars.end())
      {
        curr->d_vars.push_back(cn);
      }
      curr = &(curr->d_children[cn][0]);
    }
  }
  curr->d_data = static_cast<int64_t>(ruleIndex);
}

int64_t RewriteExecTrie::getMatch(const Node& n,
                                  std::vector<Node>& vars,
                                  std::vector<Node>& subs) const
{
  // The current (partial) substitution, used to check consistency of repeated
  // variables. vars/subs mirror its domain/range along the current path.
  std::map<Node, Node> smap;
  // Parallel stacks describing the search state, mirroring expr::MatchTrie.
  std::vector<std::vector<Node>> visit;
  std::vector<const RewriteExecTrie*> visitTrie;
  std::vector<int> visitVarIndex;
  std::vector<bool> visitBoundVar;
  visit.push_back(std::vector<Node>{n});
  visitTrie.push_back(this);
  visitVarIndex.push_back(-1);
  visitBoundVar.push_back(false);
  while (!visit.empty())
  {
    // Copy the pending symbols so that we can explore several branches from the
    // same trie node (visitVarIndex is advanced on the persisted frame).
    std::vector<Node> cvisit = visit.back();
    const RewriteExecTrie* curr = visitTrie.back();
    if (cvisit.empty())
    {
      // We consumed all of n; this is a match iff the node is a terminal.
      if (curr->d_data >= 0)
      {
        return curr->d_data;
      }
      visit.pop_back();
      visitTrie.pop_back();
      visitVarIndex.pop_back();
      visitBoundVar.pop_back();
      continue;
    }
    Node cn = cvisit.back();
    size_t index = visit.size() - 1;
    int vindex = visitVarIndex[index];
    if (vindex == -1)
    {
      // First, try to descend on the concrete operator/leaf at the front.
      if (!cn.isVar())
      {
        Node op = cn.hasOperator() ? cn.getOperator() : cn;
        uint64_t nchild = cn.hasOperator() ? cn.getNumChildren() : 0;
        std::map<Node, std::map<uint64_t, RewriteExecTrie>>::const_iterator
            ito = curr->d_children.find(op);
        if (ito != curr->d_children.end())
        {
          std::map<uint64_t, RewriteExecTrie>::const_iterator itu =
              ito->second.find(nchild);
          if (itu != ito->second.end())
          {
            cvisit.pop_back();
            if (cn.hasOperator())
            {
              for (const Node& cnc : cn)
              {
                cvisit.push_back(cnc);
              }
            }
            visit.push_back(cvisit);
            visitTrie.push_back(&itu->second);
            visitVarIndex.push_back(-1);
            visitBoundVar.push_back(false);
          }
        }
      }
      visitVarIndex[index]++;
    }
    else
    {
      // Undo a variable we bound on a previous visit to this frame.
      if (visitBoundVar[index])
      {
        Assert(!vars.empty());
        smap.erase(vars.back());
        vars.pop_back();
        subs.pop_back();
        visitBoundVar[index] = false;
      }
      if (vindex == static_cast<int>(curr->d_vars.size()))
      {
        // Exhausted all variable branches at this node.
        visit.pop_back();
        visitTrie.pop_back();
        visitVarIndex.pop_back();
        visitBoundVar.pop_back();
      }
      else
      {
        Node var = curr->d_vars[vindex];
        bool recurse = true;
        std::map<Node, Node>::iterator its = smap.find(var);
        if (its != smap.end())
        {
          // Already bound: only matches if the binding is consistent.
          if (its->second != cn)
          {
            recurse = false;
          }
        }
        else if (var.getType() != cn.getType())
        {
          recurse = false;
        }
        else
        {
          vars.push_back(var);
          subs.push_back(cn);
          smap[var] = cn;
          visitBoundVar[index] = true;
        }
        if (recurse)
        {
          cvisit.pop_back();
          std::map<Node, std::map<uint64_t, RewriteExecTrie>>::const_iterator
              ito = curr->d_children.find(var);
          Assert(ito != curr->d_children.end());
          std::map<uint64_t, RewriteExecTrie>::const_iterator itu =
              ito->second.find(0);
          Assert(itu != ito->second.end());
          visit.push_back(cvisit);
          visitTrie.push_back(&itu->second);
          visitVarIndex.push_back(-1);
          visitBoundVar.push_back(false);
        }
        visitVarIndex[index]++;
      }
    }
  }
  return -1;
}

RewriteDbExec::RewriteDbExec(NodeManager* nm) : d_nm(nm)
{
  // body is auto-generated from the RARE rules marked :exec
  addRewriteExecRules(nm, *this);
}

void RewriteDbExec::addRule(ProofRewriteRule id,
                            const Node& lhs,
                            const Node& rhs)
{
  size_t idx = d_rules.size();
  if (!expr::hasListVar(lhs))
  {
    // no list variables: index the whole left-hand side as a direct pattern
    d_rules.push_back(ExecRule{id, false, Node::null(), Node::null(), rhs});
    d_direct.addTerm(lhs, idx);
    return;
  }
  // otherwise lhs must have the restricted form (f t1 s t2); see the header.
  Assert(lhs.getNumChildren() == 3);
  Node t1 = lhs[0];
  Node needle = lhs[1];
  Node t2 = lhs[2];
  Assert(expr::isListVar(t1));
  Assert(expr::isListVar(t2));
  Assert(!expr::hasListVar(needle));
  d_rules.push_back(ExecRule{id, true, t1, t2, rhs});
  d_needleIndex[lhs.getKind()].addTerm(needle, idx);
}

Node RewriteDbExec::rewriteTop(const Node& n)
{
  std::vector<Node> vars;
  std::vector<Node> subs;
  // 1. Try direct (no-list-variable) patterns against n as a whole.
  int64_t ri = d_direct.getMatch(n, vars, subs);
  if (ri >= 0)
  {
    const ExecRule& er = d_rules[static_cast<size_t>(ri)];
    Node res = expr::narySubstitute(er.d_rhs, vars, subs);
    Trace("rewrite-exec") << "RewriteDbExec: " << n << std::endl
                          << "...via " << er.d_id << " rewrites to " << res
                          << std::endl;
    return res;
  }
  // 2. Try needle (f t1 s t2) patterns against each child of n.
  std::map<Kind, RewriteExecTrie>::const_iterator it =
      d_needleIndex.find(n.getKind());
  if (it == d_needleIndex.end())
  {
    return Node::null();
  }
  size_t nchild = n.getNumChildren();
  for (size_t i = 0; i < nchild; i++)
  {
    vars.clear();
    subs.clear();
    // try child i as the needle (f t1 s t2), where t1 is the prefix before i
    // and t2 is the suffix after i
    ri = it->second.getMatch(n[i], vars, subs);
    if (ri < 0)
    {
      continue;
    }
    const ExecRule& er = d_rules[static_cast<size_t>(ri)];
    std::vector<Node> pre(n.begin(), n.begin() + i);
    std::vector<Node> post(n.begin() + i + 1, n.end());
    std::vector<Node> allVars;
    std::vector<Node> allSubs;
    allVars.push_back(er.d_listVar1);
    allSubs.push_back(d_nm->mkNode(Kind::SEXPR, pre));
    allVars.push_back(er.d_listVar2);
    allSubs.push_back(d_nm->mkNode(Kind::SEXPR, post));
    allVars.insert(allVars.end(), vars.begin(), vars.end());
    allSubs.insert(allSubs.end(), subs.begin(), subs.end());
    Node res = expr::narySubstitute(er.d_rhs, allVars, allSubs);
    Trace("rewrite-exec") << "RewriteDbExec: " << n << std::endl
                          << "...via " << er.d_id << " rewrites to " << res
                          << std::endl;
    return res;
  }
  return Node::null();
}

Node RewriteDbExec::rewrite(const Node& n)
{
  if (d_rules.empty())
  {
    return n;
  }
  // single post-order traversal: rewrite children (bottom-up), then attempt a
  // single exec rewrite at each rebuilt node
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit{n};
  TNode cur;
  do
  {
    cur = visit.back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = Node::null();
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (it->second.isNull())
    {
      std::vector<Node> children;
      if (cur.getMetaKind() == metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      bool childChanged = false;
      for (const Node& cn : cur)
      {
        std::unordered_map<TNode, Node>::iterator itc = visited.find(cn);
        Assert(itc != visited.end());
        Assert(!itc->second.isNull());
        childChanged = childChanged || (cn != itc->second);
        children.push_back(itc->second);
      }
      Node rebuilt =
          childChanged ? d_nm->mkNode(cur.getKind(), children) : Node(cur);
      Node ex = rewriteTop(rebuilt);
      visited[cur] = ex.isNull() ? rebuilt : ex;
      visit.pop_back();
    }
    else
    {
      visit.pop_back();
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  return visited[n];
}

}  // namespace rewriter
}  // namespace cvc5::internal
