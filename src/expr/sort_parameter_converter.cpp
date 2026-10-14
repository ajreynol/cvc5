/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved. See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************/

#include "expr/sort_parameter_converter.h"

#include <algorithm>

#include "expr/array_store_all.h"
#include "expr/ascription_type.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/emptybag.h"
#include "expr/emptyset.h"
#include "expr/node_algorithm.h"
#include "expr/sequence.h"
#include "theory/quantifiers/quantifiers_attributes.h"

namespace cvc5::internal {
namespace {
void collectType(TypeNode t, std::unordered_set<TypeNode>& types)
{
  std::vector<TypeNode> pending{t};
  std::unordered_set<const DType*> datatypes;
  while (!pending.empty())
  {
    TypeNode cur = pending.back();
    pending.pop_back();
    if (!types.insert(cur).second)
    {
      continue;
    }
    if (!cur.isDatatype() || !cur.getDType().isParametric()
        || (cur.getKind() == Kind::PARAMETRIC_DATATYPE && cur.isInstantiated()))
    {
      pending.insert(pending.end(), cur.begin(), cur.end());
    }
    if (cur.isDatatype())
    {
      const DType& dt = cur.getDType();
      // The uninstantiated body has local parameters, not signature sorts.
      if (dt.isParametric()
          && (cur.getKind() != Kind::PARAMETRIC_DATATYPE
              || !cur.isInstantiated()))
        continue;
      if (!datatypes.insert(&dt).second) continue;
      for (size_t i = 0; i < dt.getNumConstructors(); ++i)
      {
        for (size_t j = 0; j < dt[i].getNumArgs(); ++j)
        {
          TypeNode field = dt[i].getArgType(j);
          if (dt.isParametric())
          {
            auto ps = dt.getParameters();
            auto rs = cur.getInstantiatedParamTypes();
            field =
                field.substitute(ps.begin(), ps.end(), rs.begin(), rs.end());
          }
          pending.push_back(field);
        }
      }
    }
  }
}
std::vector<TypeNode> parameters(const std::unordered_set<TypeNode>& types)
{
  std::vector<TypeNode> result;
  for (TypeNode t : types)
  {
    if (t.getKind() == Kind::SORT_PARAMETER_TYPE)
    {
      result.push_back(t);
    }
  }
  std::sort(result.begin(), result.end());
  return result;
}
}  // namespace

SortParameterConverter::SortParameterConverter(
    NodeManager* nm,
    const std::vector<TypeNode>& parameters,
    const std::vector<TypeNode>& replacements)
    : NodeConverter(nm, false)
{
  Assert(parameters.size() == replacements.size());
  for (size_t i = 0; i < parameters.size(); ++i)
  {
    Assert(parameters[i].getKind() == Kind::SORT_PARAMETER_TYPE);
    d_substitution.emplace(parameters[i], replacements[i]);
  }
}

Node SortParameterConverter::convert(Node n, CVC5_UNUSED bool preserveTypes)
{
  Assert(!preserveTypes);
  Assert(d_root.isNull() || d_root == n);
  d_root = n;
  expr::getVariables(n, d_originalVariables);
  return NodeConverter::convert(n, false);
}

void SortParameterConverter::collectTypes(Node n,
                                          std::unordered_set<TypeNode>& types)
{
  std::unordered_set<Node> visited;
  std::vector<Node> pending{n};
  while (!pending.empty())
  {
    Node cur = pending.back();
    pending.pop_back();
    if (!visited.insert(cur).second)
    {
      continue;
    }
    collectType(cur.getType(), types);
    pending.insert(pending.end(), cur.begin(), cur.end());
    if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      pending.push_back(cur.getOperator());
    }
    if (cur.getKind() == Kind::STORE_ALL)
    {
      pending.push_back(cur.getConst<ArrayStoreAll>().getValue());
    }
    else if (cur.getKind() == Kind::CONST_SEQUENCE)
    {
      const std::vector<Node>& elements = cur.getConst<Sequence>().getVec();
      pending.insert(pending.end(), elements.begin(), elements.end());
    }
    else if (cur.getKind() == Kind::ASCRIPTION_TYPE)
    {
      collectType(cur.getConst<AscriptionType>().getType(), types);
    }
  }
}

std::vector<TypeNode> SortParameterConverter::getParameters(TypeNode t)
{
  std::unordered_set<TypeNode> types;
  collectType(t, types);
  return parameters(types);
}

std::vector<TypeNode> SortParameterConverter::getParameters(Node n)
{
  std::unordered_set<TypeNode> types;
  collectTypes(n, types);
  return parameters(types);
}

bool SortParameterConverter::match(TypeNode pattern,
                                   TypeNode actual,
                                   std::map<TypeNode, TypeNode>& substitution)
{
  if (pattern.getKind() == Kind::SORT_PARAMETER_TYPE)
  {
    auto [it, inserted] = substitution.emplace(pattern, actual);
    return inserted || it->second == actual;
  }
  if (pattern.isFunction() && actual.isFunction())
  {
    size_t arity = pattern.getNumChildren() - 1;
    if (actual.getNumChildren() < pattern.getNumChildren()) return false;
    for (size_t i = 0; i < arity; ++i)
    {
      if (!match(pattern[i], actual[i], substitution)) return false;
    }
    std::vector<TypeNode> tail(actual.begin() + arity, actual.end());
    TypeNode range = tail.size() == 1
                         ? tail[0]
                         : actual.getNodeManager()->mkFunctionType(tail);
    return match(pattern.getRangeType(), range, substitution);
  }
  if (pattern.getKind() != actual.getKind()
      || pattern.getNumChildren() != actual.getNumChildren())
  {
    return false;
  }
  if (pattern.getNumChildren() == 0)
  {
    return pattern == actual;
  }
  for (size_t i = 0; i < pattern.getNumChildren(); ++i)
  {
    if (!match(pattern[i], actual[i], substitution))
    {
      return false;
    }
  }
  return true;
}

Node SortParameterConverter::inferApplication(
    Node op, const std::vector<Node>& arguments)
{
  TypeNode type = op.getType();
  if (op.getKind() != Kind::VARIABLE
      || op.hasAttribute(SortParameterOriginAttr()) || !type.isFunction()
      || !type.hasSortParameter()
      || arguments.size() > type.getNumChildren() - 1)
  {
    return op;
  }
  std::map<TypeNode, TypeNode> substitution;
  for (size_t i = 0; i < arguments.size(); ++i)
  {
    if (!match(type[i], arguments[i].getType(), substitution))
    {
      // The ordinary application type checker reports the mismatch.
      return op;
    }
  }
  std::vector<TypeNode> from, to;
  for (const auto& [p, t] : substitution)
  {
    from.push_back(p);
    to.push_back(t);
  }
  SortParameterConverter converter(op.getNodeManager(), from, to);
  return converter.convert(op, false);
}

TypeNode SortParameterConverter::postConvertType(TypeNode t)
{
  auto it = d_substitution.find(t);
  if (it != d_substitution.end()) return it->second;
  if (t.isFunction())
  {
    // Instantiating a result parameter with a function sort introduces
    // currying, represented internally by a flat function type.
    return d_nm->mkFunctionType(std::vector<TypeNode>(t.begin(), t.end()));
  }
  return t;
}

Node SortParameterConverter::postConvertUntyped(
    Node original, const std::vector<Node>& children, bool changed)
{
  Kind k = original.getKind();
  TypeNode type = original.getType();
  TypeNode target = convertType(type);
  if (k == Kind::APPLY_UF && changed && target.isFunction())
  {
    return d_nm->mkLeftAssociative(Kind::HO_APPLY, children);
  }
  if ((k == Kind::VARIABLE || k == Kind::BOUND_VARIABLE) && target != type)
  {
    Node instance;
    size_t index = 0;
    do
    {
      instance = d_nm->mkSortParameterInstance(original, target, index++);
    } while (k == Kind::BOUND_VARIABLE && d_originalVariables.count(instance));
    return instance;
  }
  if (k == Kind::ASCRIPTION_TYPE)
  {
    TypeNode ascribed = original.getConst<AscriptionType>().getType();
    return d_nm->mkConst(AscriptionType(convertType(ascribed)));
  }
  if (k == Kind::STORE_ALL)
  {
    Node value = NodeConverter::convert(
        original.getConst<ArrayStoreAll>().getValue(), false);
    return d_nm->mkConst(ArrayStoreAll(target, value));
  }
  if (k == Kind::CONST_SEQUENCE && target != type)
  {
    std::vector<Node> elements;
    for (Node element : original.getConst<Sequence>().getVec())
    {
      elements.push_back(NodeConverter::convert(element, false));
    }
    return d_nm->mkConst(Sequence(target.getSequenceElementType(), elements));
  }
  if (target != type)
  {
    if (k == Kind::SET_EMPTY) return d_nm->mkConst(EmptySet(target));
    if (k == Kind::BAG_EMPTY) return d_nm->mkConst(EmptyBag(target));
    if (k == Kind::SET_UNIVERSE || k == Kind::SEP_NIL)
    {
      return d_nm->mkNullaryOperator(target, k);
    }
  }
  Node result = changed ? d_nm->mkNode(k, children) : original;
  if (original.getAttribute(theory::FunDefAttribute()))
  {
    result.setAttribute(theory::FunDefAttribute(), true);
  }
  return result;
}

}  // namespace cvc5::internal
