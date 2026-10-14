/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved. See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************/

#include "cvc5_private.h"

#ifndef CVC5__EXPR__SORT_PARAMETER_CONVERTER_H
#define CVC5__EXPR__SORT_PARAMETER_CONVERTER_H

#include "expr/attribute.h"
#include "expr/node_converter.h"

namespace cvc5::internal {

/** The declaration underlying an instance of a polymorphic symbol. */
using SortParameterOriginAttr =
    expr::Attribute<struct SortParameterOriginTag, Node>;

/** Simultaneous, capture-avoiding substitution of global sort parameters. */
class SortParameterConverter : public NodeConverter
{
 public:
  SortParameterConverter(NodeManager* nm,
                         const std::vector<TypeNode>& parameters,
                         const std::vector<TypeNode>& replacements);
  /** Convert one term, avoiding capture by variables already in that term. */
  Node convert(Node n, bool preserveTypes = false);
  /** Collect types, including types hidden in operators and constant values. */
  static void collectTypes(Node n, std::unordered_set<TypeNode>& types);
  /** Collect the global parameters occurring in a type/term, in id order. */
  static std::vector<TypeNode> getParameters(TypeNode t);
  static std::vector<TypeNode> getParameters(Node n);
  /** Match a rank component. Only parameters in the pattern are flexible. */
  static bool match(TypeNode pattern,
                    TypeNode actual,
                    std::map<TypeNode, TypeNode>& substitution);
  /** Specialize a free function for an application, leaving bound maps alone.
   */
  static Node inferApplication(Node op, const std::vector<Node>& arguments);

 protected:
  TypeNode postConvertType(TypeNode t) override;
  Node postConvertUntyped(Node original,
                          const std::vector<Node>& children,
                          bool changed) override;

 private:
  std::map<TypeNode, TypeNode> d_substitution;
  Node d_root;
  std::unordered_set<Node> d_originalVariables;
};

}  // namespace cvc5::internal
#endif
