/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The executable rewrite database.
 *
 * This is the template of rewrite_db_exec.cpp. Everything but the body marked
 * below is written by hand and is *not* regenerated: only the implementation
 * of the :exec rules is, by `-o rare-db-exec`, which contrib/install-rare-
 * rewrites substitutes into this template.
 */

#include "expr/aci_norm.h"
#include "expr/nary_term_util.h"
#include "expr/node_manager.h"
#include "rewriter/rewrite_db_exec.h"
#include "theory/builtin/generic_op.h"
#include "util/bitvector.h"
#include "util/rational.h"
#include "util/string.h"

namespace cvc5::internal {
namespace rewriter {

Node RewriteDbExec::mkListArg(const Node& n, size_t start, size_t end) const
{
  Assert(start <= end && end <= n.getNumChildren());
  std::vector<Node> children(n.begin() + start, n.begin() + end);
  return d_nm->mkNode(Kind::SEXPR, children);
}

Node RewriteDbExec::instantiate(const Node& p, const ExecMatch& m) const
{
  std::map<ProofRewriteRule, std::vector<Node>>::const_iterator it =
      d_ruleVars.find(m.d_id);
  Assert(it != d_ruleVars.end());
  Assert(it->second.size() == m.d_subs.size());
  // Note this splices the :list variables, and may fail e.g. if a list
  // variable bound to the empty sequence leaves an application whose kind has
  // no null terminator.
  Node r = expr::narySubstitute(p, it->second, m.d_subs);
  if (r.isNull())
  {
    return r;
  }
  return toConcrete(r);
}

Node RewriteDbExec::toConcrete(const Node& n) const
{
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit{n};
  do
  {
    TNode cur = visit.back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = Node::null();
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    visit.pop_back();
    if (!it->second.isNull())
    {
      continue;
    }
    Node ret = cur;
    bool childChanged = false;
    std::vector<Node> children;
    if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      children.push_back(cur.getOperator());
    }
    for (const Node& cn : cur)
    {
      it = visited.find(cn);
      Assert(it != visited.end() && !it->second.isNull());
      childChanged = childChanged || cn != it->second;
      children.push_back(it->second);
    }
    if (childChanged)
    {
      ret = d_nm->mkNode(cur.getKind(), children);
    }
    if (ret.getKind() == Kind::APPLY_INDEXED_SYMBOLIC)
    {
      // the indices are concrete by now, hence this is the application the
      // symbolic term denotes
      ret = GenericOp::getConcreteApp(ret);
    }
    visited[cur] = ret;
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  return visited[n];
}

size_t RewriteDbExec::getNumConditions(const ExecMatch& m) const
{
  std::map<ProofRewriteRule, std::vector<Node>>::const_iterator it =
      d_ruleConds.find(m.d_id);
  return it == d_ruleConds.end() ? 0 : it->second.size();
}

Node RewriteDbExec::getCondition(const ExecMatch& m, size_t i) const
{
  std::map<ProofRewriteRule, std::vector<Node>>::const_iterator it =
      d_ruleConds.find(m.d_id);
  Assert(it != d_ruleConds.end() && i < it->second.size());
  return instantiate(it->second[i], m);
}

Node RewriteDbExec::getResult(const ExecMatch& m) const
{
  std::map<ProofRewriteRule, Node>::const_iterator it = d_ruleRhs.find(m.d_id);
  Assert(it != d_ruleRhs.end());
  return instantiate(it->second, m);
}

// The implementation of the :exec rules below is generated, see the note at
// the top of this file.
// clang-format off
${exec_impl}$
// clang-format on

}  // namespace rewriter
}  // namespace cvc5::internal
