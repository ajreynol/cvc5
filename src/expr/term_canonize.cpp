/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of term canonize.
 */

#include "expr/term_canonize.h"

#include <sstream>

#include "expr/bound_var_manager.h"
// TODO #1216: move the code in this include
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "theory/quantifiers/term_util.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace expr {

TermCanonize::TermCanonize(TypeClassCallback* tcc,
                           bool applyTOrder,
                           bool doHoVar,
                           bool applyGTerms)
    : d_tcc(tcc),
      d_applyTOrder(applyTOrder),
      d_doHoVar(doHoVar),
      d_applyGTerms(applyGTerms)
{
}

bool TermCanonize::getTermOrder(Node a, Node b)
{
  if (a.getKind() == Kind::BOUND_VARIABLE)
  {
    if (b.getKind() == Kind::BOUND_VARIABLE)
    {
      // just use builtin node comparison
      return a < b;
    }
    return true;
  }
  if (b.getKind() != Kind::BOUND_VARIABLE)
  {
    Node aop = a.hasOperator() ? a.getOperator() : a;
    Node bop = b.hasOperator() ? b.getOperator() : b;
    Trace("aeq-debug2") << a << "...op..." << aop << std::endl;
    Trace("aeq-debug2") << b << "...op..." << bop << std::endl;
    if (aop == bop)
    {
      if (a.getNumChildren() == b.getNumChildren())
      {
        for (size_t i = 0, size = a.getNumChildren(); i < size; i++)
        {
          if (a[i] != b[i])
          {
            // first distinct child determines the ordering
            return getTermOrder(a[i], b[i]);
          }
        }
      }
      else
      {
        return a.getNumChildren() < b.getNumChildren();
      }
    }
    else
    {
      return aop < bop;
    }
  }
  return false;
}

Node TermCanonize::getCanonicalFreeVar(TypeNode tn, size_t i, uint32_t tc)
{
  return getCanonicalFreeSymInternal(tn, i, tc, 0);
}

Node TermCanonize::getCanonicalFreeConstant(TypeNode tn, size_t i, uint32_t tc)
{
  return getCanonicalFreeSymInternal(tn, i, tc, 1);
}

Node TermCanonize::getCanonicalFreeSymInternal(TypeNode tn,
                                               size_t i,
                                               uint32_t tc,
                                               size_t index)
{
  Assert(!tn.isNull());
  std::pair<TypeNode, uint32_t> key(tn, tc);
  std::vector<Node>& tvars = d_cn_free_var[index][key];
  while (tvars.size() <= i)
  {
    std::stringstream os;
    if (tn.isFunction())
    {
      os << "f" << i;
    }
    else
    {
      std::stringstream oss;
      oss << tn;
      std::string typ_name = oss.str();
      while (typ_name[0] == '(')
      {
        typ_name.erase(typ_name.begin());
      }
      os << typ_name[0] << i;
    }
    NodeManager* nm = tn.getNodeManager();
    Node x;
    if (index == 0)
    {
      BoundVarManager* bvm = nm->getBoundVarManager();
      Node cacheVal = BoundVarManager::getCacheValue(
          BoundVarManager::getCacheValue(nm, tc), i);
      x = bvm->mkBoundVar(BoundVarId::TERM_CANONIZE, cacheVal, os.str(), tn);
    }
    else
    {
      x = nm->getSkolemManager()->mkDummySkolem(os.str(), tn);
    }
    d_fvIndex[x] = tvars.size();
    tvars.push_back(x);
  }
  return tvars[i];
}

uint32_t TermCanonize::getTypeClass(TNode v)
{
  return d_tcc == nullptr ? 0 : d_tcc->getTypeClass(v);
}

size_t TermCanonize::getIndexForFreeVariable(Node v) const
{
  std::map<Node, size_t>::const_iterator it = d_fvIndex.find(v);
  if (it == d_fvIndex.end())
  {
    return 0;
  }
  return it->second;
}

struct sortTermOrder
{
  TermCanonize* d_tu;
  bool operator()(Node i, Node j) { return d_tu->getTermOrder(i, j); }
};

Node TermCanonize::getCanonicalTerm(
    TNode n,
    std::map<std::pair<TypeNode, uint32_t>, unsigned>& vcount,
    std::map<std::pair<TypeNode, uint32_t>, unsigned>& ccount,
    std::map<TNode, Node>& visited)
{
  std::map<TNode, Node>::iterator it = visited.find(n);
  if (it != visited.end())
  {
    return it->second;
  }

  Trace("canon-term-debug") << "Get canonical term for " << n << std::endl;
  if (n.getKind() == Kind::BOUND_VARIABLE)
  {
    uint32_t tc = getTypeClass(n);
    TypeNode tn = n.getType();
    std::pair<TypeNode, uint32_t> key(tn, tc);
    // allocate variable
    unsigned vn = vcount[key];
    vcount[key]++;
    Node fv = getCanonicalFreeVar(tn, vn, tc);
    visited[n] = fv;
    Trace("canon-term-debug") << "...allocate variable " << fv << std::endl;
    return fv;
  }
  else if (n.getNumChildren() > 0)
  {
    // collect children
    Trace("canon-term-debug") << "Collect children" << std::endl;
    std::vector<Node> cchildren;
    for (const Node& cn : n)
    {
      cchildren.push_back(cn);
    }
    // make canonical if non-ground
    if (expr::hasBoundVar(n))
    {
      Trace("canon-term-debug") << "Make canonical children" << std::endl;
      for (unsigned i = 0, size = cchildren.size(); i < size; i++)
      {
        cchildren[i] = getCanonicalTerm(cchildren[i], vcount, ccount, visited);
      }
    }
    else if (d_applyGTerms)
    {
      // n is ground: replace it wholesale by a canonical free constant
      uint32_t tc = getTypeClass(n);
      TypeNode tn = n.getType();
      std::pair<TypeNode, uint32_t> key(tn, tc);
      // allocate constant
      unsigned vn = ccount[key];
      ccount[key]++;
      Node k = getCanonicalFreeConstant(tn, vn, tc);
      visited[n] = k;
      Trace("canon-term-debug") << "...allocate constant " << k << std::endl;
      return k;
    }
    // if applicable, sort by term order
    if (d_applyTOrder && theory::quantifiers::TermUtil::isComm(n.getKind()))
    {
      Trace("canon-term-debug")
          << "Sort based on commutative operator " << n.getKind() << std::endl;
      sortTermOrder sto;
      sto.d_tu = this;
      std::sort(cchildren.begin(), cchildren.end(), sto);
    }
    if (n.getMetaKind() == metakind::PARAMETERIZED)
    {
      Node op = n.getOperator();
      if (d_doHoVar)
      {
        op = getCanonicalTerm(op, vcount, ccount, visited);
      }
      Trace("canon-term-debug") << "Insert operator " << op << std::endl;
      cchildren.insert(cchildren.begin(), op);
    }
    Trace("canon-term-debug")
        << "...constructing for " << n << "." << std::endl;
    Node ret = n.getNodeManager()->mkNode(n.getKind(), cchildren);
    Trace("canon-term-debug")
        << "...constructed " << ret << " for " << n << "." << std::endl;
    visited[n] = ret;
    return ret;
  }
  Trace("canon-term-debug") << "...return 0-child term." << std::endl;
  return n;
}

Node TermCanonize::getCanonicalTerm(TNode n)
{
  std::map<std::pair<TypeNode, uint32_t>, unsigned> vcount;
  std::map<std::pair<TypeNode, uint32_t>, unsigned> ccount;
  std::map<TNode, Node> visited;
  return getCanonicalTerm(n, vcount, ccount, visited);
}

Node TermCanonize::getCanonicalTerm(TNode n, std::map<TNode, Node>& visited)
{
  std::map<std::pair<TypeNode, uint32_t>, unsigned> vcount;
  std::map<std::pair<TypeNode, uint32_t>, unsigned> ccount;
  return getCanonicalTerm(n, vcount, ccount, visited);
}

}  // namespace expr
}  // namespace cvc5::internal
