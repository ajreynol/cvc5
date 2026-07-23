/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of Logos proof conversion.
 */

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "proof/eo/logos_node_converter.h"
#include "test_smt.h"

namespace cvc5::internal {
namespace test {

using namespace proof;

class TestLogosNodeConverterBlack : public TestSmt
{
};

TEST_F(TestLogosNodeConverterBlack, datatypeDefaultOrder)
{
  TypeNode unresA = d_nodeManager->mkSort("A");
  TypeNode unresB = d_nodeManager->mkSort("B");
  TypeNode unresC = d_nodeManager->mkSort("C");

  // A has to use B to construct a value.
  DType a("A");
  std::shared_ptr<DTypeConstructor> mkA =
      std::make_shared<DTypeConstructor>("mkA");
  mkA->addArg("b", unresB);
  a.addConstructor(mkA);

  // B can use either A or C. Since A relies on B, its default must use C.
  DType b("B");
  std::shared_ptr<DTypeConstructor> mkBA =
      std::make_shared<DTypeConstructor>("mkBA");
  mkBA->addArg("a", unresA);
  b.addConstructor(mkBA);
  std::shared_ptr<DTypeConstructor> mkBC =
      std::make_shared<DTypeConstructor>("mkBC");
  mkBC->addArg("c", unresC);
  b.addConstructor(mkBC);

  // C can use A but also has a base constructor.
  DType c("C");
  std::shared_ptr<DTypeConstructor> mkCA =
      std::make_shared<DTypeConstructor>("mkCA");
  mkCA->addArg("a", unresA);
  c.addConstructor(mkCA);
  c.addConstructor(std::make_shared<DTypeConstructor>("leaf"));

  std::vector<DType> datatypes;
  datatypes.push_back(a);
  datatypes.push_back(b);
  datatypes.push_back(c);
  std::vector<TypeNode> types =
      d_nodeManager->mkMutualDatatypeTypes(datatypes);

  // Start at C so that the discovery order is C, A, B. The declaration must
  // instead be A, B, C: A's default uses B, B's uses C, and C uses leaf.
  LogosNodeConverter converter(d_nodeManager.get());
  Node type = converter.typeAsNode(types[2]);
  ASSERT_EQ(type.getNumChildren(), 2);
  Node declaration = type[1];
  for (const char* name : {"A", "B", "C"})
  {
    ASSERT_EQ(declaration.getNumChildren(), 3);
    ASSERT_EQ(declaration.getOperator().getName(), "DatatypeDecl.cons");
    std::string expected =
        std::string("(SmtEval.native_string_lit \"") + name + "\")";
    ASSERT_EQ(declaration[0].getName(), expected);
    declaration = declaration[2];
  }
  ASSERT_EQ(declaration.getName(), "DatatypeDecl.nil");
}

}  // namespace test
}  // namespace cvc5::internal
