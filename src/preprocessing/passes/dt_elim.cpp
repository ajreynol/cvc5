/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inline single-constructor datatypes.
 */

#include "preprocessing/passes/dt_elim.h"

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/node_manager.h"
#include "preprocessing/assertion_pipeline.h"
#include "smt/logic_exception.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/datatypes/theory_datatypes_utils.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

namespace dtutils = theory::datatypes::utils;

namespace {

bool isProduct(TypeNode tn)
{
  return tn.isDatatype() && tn.getDType().getNumConstructors() == 1;
}

}  // namespace

DtElim::DtElim(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "dt-elim")
{
}

bool DtElim::changesType(TypeNode tn)
{
  const Types& ts = convertType(tn);
  return ts.size() != 1 || ts[0] != tn;
}

const DtElim::Types& DtElim::convertType(TypeNode tn)
{
  auto it = d_types.find(tn);
  if (it != d_types.end())
  {
    return it->second;
  }
  // Discover the entire dependency graph, including constructor fields (which
  // are not children of a datatype TypeNode). Use reverse edges to propagate
  // changes through mutually recursive datatypes.
  std::unordered_map<TypeNode, Types> parents;
  std::unordered_set<TypeNode> seen;
  std::unordered_set<TypeNode> changed;
  Types visit{tn};
  Types types;
  Types pending;
  while (!visit.empty())
  {
    TypeNode t = visit.back();
    visit.pop_back();
    if (!seen.insert(t).second)
    {
      continue;
    }
    auto itc = d_types.find(t);
    if (itc != d_types.end())
    {
      if (itc->second.size() != 1 || itc->second[0] != t)
      {
        pending.push_back(t);
      }
      continue;
    }
    types.push_back(t);
    Types deps;
    if (t.isDatatype())
    {
      const DType& dt = t.getDType();
      // Expanding the concrete instances of a nested recursive datatype need
      // not terminate, e.g. D[T] with a field D[D[T]].
      if (dt.hasNestedRecursion())
      {
        throw LogicException(
            "dt-elim does not support nested recursive datatype "
            + t.toString());
      }
      if (isProduct(t))
      {
        pending.push_back(t);
      }
      for (size_t i = 0; i < dt.getNumConstructors(); ++i)
      {
        TypeNode ct = dt[i].getInstantiatedConstructorType(t);
        for (size_t j = 0; j < dt[i].getNumArgs(); ++j)
        {
          deps.push_back(ct[j]);
        }
      }
    }
    else
    {
      deps.assign(t.begin(), t.end());
    }
    for (TypeNode dep : deps)
    {
      parents[dep].push_back(t);
      visit.push_back(dep);
    }
  }
  while (!pending.empty())
  {
    TypeNode t = pending.back();
    pending.pop_back();
    if (changed.insert(t).second)
    {
      const Types& ps = parents[t];
      pending.insert(pending.end(), ps.begin(), ps.end());
    }
  }
  // Reject contexts without an inlining interpretation before creating any
  // replacement types. Even a product with one field changes representation.
  for (TypeNode t : types)
  {
    if (changed.count(t) == 0)
    {
      continue;
    }
    if ((!t.isDatatype() && !t.isFunction())
        || (t.isDatatype()
            && (t.getDType().isCodatatype() || t.getDType().isSygus())))
    {
      throw LogicException("dt-elim cannot inline datatype in type "
                           + t.toString());
    }
  }
  NodeManager* nm = nodeManager();
  Types rebuilt;
  Types unresolved;
  std::vector<DType> datatypes;
  for (TypeNode t : types)
  {
    if (changed.count(t) == 0)
    {
      d_types[t] = {t};
    }
    else if (t.isDatatype() && !isProduct(t))
    {
      std::string name = "dt_elim_" + std::to_string(t.getId());
      TypeNode u = nm->mkUnresolvedDatatypeSort(name);
      rebuilt.push_back(t);
      unresolved.push_back(u);
      datatypes.emplace_back(name);
      d_types[t] = {u};
    }
  }
  std::unordered_set<TypeNode> active;
  for (TypeNode t : types)
  {
    flattenType(t, active);
  }
  for (size_t i = 0; i < rebuilt.size(); ++i)
  {
    TypeNode t = rebuilt[i];
    const DType& dt = t.getDType();
    for (size_t j = 0; j < dt.getNumConstructors(); ++j)
    {
      auto cons = std::make_shared<DTypeConstructor>(dt[j].getName());
      TypeNode ct = dt[j].getInstantiatedConstructorType(t);
      size_t index = 0;
      for (size_t k = 0; k < dt[j].getNumArgs(); ++k)
      {
        for (TypeNode ft : d_types.at(ct[k]))
        {
          cons->addArg("field_" + std::to_string(index++), ft);
        }
      }
      datatypes[i].addConstructor(cons);
    }
  }
  if (!datatypes.empty())
  {
    Types resolved = nm->mkMutualDatatypeTypes(datatypes);
    for (TypeNode t : types)
    {
      for (TypeNode& ct : d_types.at(t))
      {
        ct = ct.substitute(unresolved.begin(),
                           unresolved.end(),
                           resolved.begin(),
                           resolved.end());
      }
    }
    // The new types are already translated. This matters when incremental
    // preprocessing sees assertions containing symbols created by this pass.
    for (TypeNode t : resolved)
    {
      d_types[t] = {t};
    }
  }
  return d_types.at(tn);
}

const DtElim::Types& DtElim::flattenType(TypeNode tn,
                                         std::unordered_set<TypeNode>& active)
{
  auto it = d_types.find(tn);
  if (it != d_types.end())
  {
    return it->second;
  }
  if (!active.insert(tn).second)
  {
    throw LogicException("dt-elim cannot inline recursive product "
                         + tn.toString());
  }
  Types result;
  if (isProduct(tn))
  {
    const DTypeConstructor& c = tn.getDType()[0];
    TypeNode ct = c.getInstantiatedConstructorType(tn);
    for (size_t i = 0; i < c.getNumArgs(); ++i)
    {
      const Types& ts = flattenType(ct[i], active);
      result.insert(result.end(), ts.begin(), ts.end());
    }
  }
  else
  {
    Assert(tn.isFunction());
    Types domain;
    for (TypeNode arg : tn.getArgTypes())
    {
      const Types& ts = flattenType(arg, active);
      domain.insert(domain.end(), ts.begin(), ts.end());
    }
    for (TypeNode range : flattenType(tn.getRangeType(), active))
    {
      result.push_back(domain.empty()
                           ? range
                           : nodeManager()->mkFunctionType(domain, range));
    }
  }
  active.erase(tn);
  return d_types.emplace(tn, result).first->second;
}

DtElim::Terms DtElim::children(Node n, size_t begin, size_t end) const
{
  Terms result;
  for (size_t i = begin; i < end; ++i)
  {
    const Terms& cs = d_terms.at(n[i]);
    result.insert(result.end(), cs.begin(), cs.end());
  }
  return result;
}

Node DtElim::equal(const Terms& a, const Terms& b) const
{
  Assert(a.size() == b.size());
  Terms eqs;
  for (size_t i = 0; i < a.size(); ++i)
  {
    eqs.push_back(a[i].eqNode(b[i]));
  }
  return nodeManager()->mkAnd(eqs);
}

std::pair<size_t, size_t> DtElim::fieldRange(TypeNode tn, size_t ci, size_t si)
{
  TypeNode ct = tn.getDType()[ci].getInstantiatedConstructorType(tn);
  size_t start = 0;
  for (size_t i = 0; i < si; ++i)
  {
    start += convertType(ct[i]).size();
  }
  return {start, start + convertType(ct[si]).size()};
}

const DtElim::Terms& DtElim::convert(Node n)
{
  std::vector<std::pair<Node, bool>> visit{{n, false}};
  while (!visit.empty())
  {
    Node cur = visit.back().first;
    bool ready = visit.back().second;
    visit.pop_back();
    if (d_terms.find(cur) != d_terms.end())
    {
      continue;
    }
    if (!ready)
    {
      if (cur.getKind() == Kind::MATCH)
      {
        Node expanded = theory::datatypes::DatatypesRewriter::expandMatch(cur);
        d_terms[cur] = convert(expanded);
        continue;
      }
      visit.emplace_back(cur, true);
      if (cur.getKind() == Kind::APPLY_UF)
      {
        visit.emplace_back(cur.getOperator(), false);
      }
      // Annotations use the same translation as the body, including symbols
      // that occur only in a pattern and the components of bound variables.
      for (size_t i = 0; i < cur.getNumChildren(); ++i)
      {
        visit.emplace_back(cur[i], false);
      }
    }
    else
    {
      d_terms[cur] = convertNode(cur);
    }
  }
  return d_terms.at(n);
}

DtElim::Terms DtElim::convertNode(Node n)
{
  NodeManager* nm = nodeManager();
  Kind k = n.getKind();
  if (k == Kind::BOUND_VAR_LIST)
  {
    return children(n, 0, n.getNumChildren());
  }
  if (k == Kind::INST_PATTERN || k == Kind::INST_PATTERN_LIST)
  {
    // Keep all components of a pattern term in the same multi-pattern. In
    // particular, splitting f(x) must not turn the terms of an existing
    // multi-pattern into independent alternatives. Separate INST_PATTERN
    // children of a pattern list remain separate alternatives.
    Terms cs = children(n, 0, n.getNumChildren());
    // Terms of a nullary product disappear. Neither an empty pattern nor an
    // empty pattern list is a valid node.
    return cs.empty() ? Terms{} : Terms{nm->mkNode(k, cs)};
  }
  if (k == Kind::INST_NO_PATTERN)
  {
    // A no-pattern excludes one term, so exclude each component separately.
    Terms result;
    for (Node c : d_terms.at(n[0]))
    {
      result.push_back(nm->mkNode(k, c));
    }
    return result;
  }
  TypeNode tn = n.getType();
  const Types& ts = convertType(tn);
  bool changed = changesType(tn);
  if (n.isVar())
  {
    if (!changed)
    {
      return {n};
    }
    Terms result;
    for (TypeNode t : ts)
    {
      result.push_back(k == Kind::BOUND_VARIABLE
                           ? NodeManager::mkBoundVar(t)
                           : NodeManager::mkDummySkolem("dt_elim", t));
    }
    return result;
  }
  if (k == Kind::FORALL || k == Kind::EXISTS || k == Kind::LAMBDA)
  {
    const Terms& vars = d_terms.at(n[0]);
    const Terms& body = d_terms.at(n[1]);
    if (vars.empty())
    {
      return body;
    }
    Node bvl = nm->mkNode(Kind::BOUND_VAR_LIST, vars);
    Terms result;
    for (Node b : body)
    {
      Terms cs{bvl, b};
      if (n.getNumChildren() == 3)
      {
        const Terms& annotations = d_terms.at(n[2]);
        cs.insert(cs.end(), annotations.begin(), annotations.end());
      }
      result.push_back(nm->mkNode(k, cs));
    }
    return result;
  }
  if (k == Kind::APPLY_UF)
  {
    Terms args = children(n, 0, n.getNumChildren());
    Terms result;
    for (Node op : d_terms.at(n.getOperator()))
    {
      if (args.empty())
      {
        result.push_back(op);
      }
      else if (args.size() < op.getType().getArgTypes().size())
      {
        // A function-valued field of the original result becomes a curried
        // result of this component function.
        for (Node arg : args)
        {
          op = nm->mkNode(Kind::HO_APPLY, op, arg);
        }
        result.push_back(op);
      }
      else
      {
        Terms cs{op};
        cs.insert(cs.end(), args.begin(), args.end());
        result.push_back(nm->mkNode(Kind::APPLY_UF, cs));
      }
    }
    return result;
  }
  if (k == Kind::HO_APPLY)
  {
    Terms result;
    for (Node op : d_terms.at(n[0]))
    {
      for (Node arg : d_terms.at(n[1]))
      {
        op = nm->mkNode(Kind::HO_APPLY, op, arg);
      }
      result.push_back(op);
    }
    return result;
  }
  if (k == Kind::APPLY_CONSTRUCTOR)
  {
    Terms args = children(n, 0, n.getNumChildren());
    if (isProduct(tn))
    {
      return args;
    }
    TypeNode target = ts[0];
    return {dtutils::mkApplyCons(
        target, target.getDType(), dtutils::indexOf(n.getOperator()), args)};
  }
  if (k == Kind::APPLY_SELECTOR || k == Kind::APPLY_TESTER
      || k == Kind::APPLY_UPDATER)
  {
    TypeNode dt = n[0].getType();
    const Terms& obj = d_terms.at(n[0]);
    size_t ci = k == Kind::APPLY_TESTER ? dtutils::indexOf(n.getOperator())
                                        : dtutils::cindexOf(n.getOperator());
    if (k == Kind::APPLY_TESTER)
    {
      return {isProduct(dt)
                  ? nm->mkConst(true)
                  : dtutils::mkTester(obj[0], ci, obj[0].getType().getDType())};
    }
    size_t si = dtutils::indexOf(n.getOperator());
    auto [start, end] = fieldRange(dt, ci, si);
    if (k == Kind::APPLY_SELECTOR)
    {
      if (isProduct(dt))
      {
        return Terms(obj.begin() + start, obj.begin() + end);
      }
      const DTypeConstructor& c = obj[0].getType().getDType()[ci];
      Terms result;
      for (size_t i = start; i < end; ++i)
      {
        result.push_back(
            nm->mkNode(Kind::APPLY_SELECTOR, c[i].getSelector(), obj[0]));
      }
      return result;
    }
    const Terms& value = d_terms.at(n[1]);
    if (isProduct(dt))
    {
      Terms result(obj.begin(), obj.begin() + start);
      result.insert(result.end(), value.begin(), value.end());
      result.insert(result.end(), obj.begin() + end, obj.end());
      return result;
    }
    TypeNode target = obj[0].getType();
    const DType& newDt = target.getDType();
    const DTypeConstructor& c = newDt[ci];
    Terms args;
    for (size_t i = 0; i < c.getNumArgs(); ++i)
    {
      args.push_back(
          i >= start && i < end
              ? value[i - start]
              : nm->mkNode(Kind::APPLY_SELECTOR, c[i].getSelector(), obj[0]));
    }
    Node updated = dtutils::mkApplyCons(target, newDt, ci, args);
    return {nm->mkNode(
        Kind::ITE, dtutils::mkTester(obj[0], ci, newDt), updated, obj[0])};
  }
  if (k == Kind::EQUAL)
  {
    return {equal(d_terms.at(n[0]), d_terms.at(n[1]))};
  }
  if (k == Kind::DISTINCT && changesType(n[0].getType()))
  {
    Terms pairs;
    for (size_t i = 0; i < n.getNumChildren(); ++i)
    {
      for (size_t j = i + 1; j < n.getNumChildren(); ++j)
      {
        pairs.push_back(equal(d_terms.at(n[i]), d_terms.at(n[j])).negate());
      }
    }
    return {nm->mkAnd(pairs)};
  }
  if (k == Kind::ITE)
  {
    const Terms& a = d_terms.at(n[1]);
    const Terms& b = d_terms.at(n[2]);
    Terms result;
    for (size_t i = 0; i < a.size(); ++i)
    {
      result.push_back(nm->mkNode(k, d_terms.at(n[0])[0], a[i], b[i]));
    }
    return result;
  }
  // Operators from other theories are preserved only if all argument/result
  // types stay the same. Never rebuild an operator with an incompatible type
  // or silently retain a product datatype that should have been eliminated.
  Terms cs;
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    cs.push_back(n.getOperator());
  }
  bool childChanged = false;
  for (Node c : n)
  {
    const Terms& ct = d_terms.at(c);
    if (c.getKind() == Kind::BOUND_VAR_LIST)
    {
      // Other binders, e.g. WITNESS, can be kept only when their variables
      // retain their types. In particular, separate witnesses for product
      // components would not necessarily choose a consistent tuple.
      bool sameTypes = ct.size() == c.getNumChildren();
      for (size_t i = 0; sameTypes && i < ct.size(); ++i)
      {
        sameTypes = ct[i].getType() == c[i].getType();
      }
      if (!sameTypes)
      {
        changed = true;
        break;
      }
      Node bvl = nm->mkNode(Kind::BOUND_VAR_LIST, ct);
      childChanged = childChanged || bvl != c;
      cs.push_back(bvl);
      continue;
    }
    if (ct.size() != 1 || ct[0].getType() != c.getType())
    {
      changed = true;
      break;
    }
    childChanged = childChanged || ct[0] != c;
    cs.push_back(ct[0]);
  }
  if (changed)
  {
    throw LogicException("dt-elim cannot translate operator "
                         + kindToString(k));
  }
  return {childChanged ? nm->mkNode(k, cs) : n};
}

PreprocessingPassResult DtElim::applyInternal(AssertionPipeline* assertions)
{
  for (size_t i = 0, size = assertions->size(); i < size; ++i)
  {
    Node prev = (*assertions)[i];
    const Terms& result = convert(prev);
    Assert(result.size() == 1);
    if (result[0] != prev)
    {
      Trace("dt-elim") << prev << " -> " << result[0] << std::endl;
      assertions->replace(i, result[0], nullptr, TrustId::PREPROCESS_DT_ELIM);
      assertions->ensureRewritten(i);
      if (assertions->isInConflict())
      {
        return PreprocessingPassResult::CONFLICT;
      }
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
