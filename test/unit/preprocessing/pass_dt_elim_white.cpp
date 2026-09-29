/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Tests for product datatype elimination.
 */

#include "expr/dtype.h"
#include "expr/node_algorithm.h"
#include "preprocessing/passes/dt_elim.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/logic_exception.h"
#include "test_smt.h"
#include "util/rational.h"
#include "util/string.h"

namespace cvc5::internal {
namespace test {

using namespace preprocessing;
using namespace preprocessing::passes;

class TestPPWhiteDtElim : public TestSmt
{
 protected:
  void SetUp() override
  {
    TestSmt::SetUp();
    d_context = std::make_unique<PreprocessingPassContext>(
        d_slvEngine->getEnv(), nullptr, nullptr, nullptr);
    d_pass = std::make_unique<DtElim>(d_context.get());
    d_int = d_nodeManager->integerType();
    d_bool = d_nodeManager->booleanType();
    d_pair = product("Pair", {d_int, d_bool});
  }

  TypeNode product(const std::string& name, const std::vector<TypeNode>& fields)
  {
    DType dt(name);
    auto c = std::make_shared<DTypeConstructor>("mk_" + name);
    for (size_t i = 0; i < fields.size(); ++i)
    {
      c->addArg("field" + std::to_string(i), fields[i]);
    }
    dt.addConstructor(c);
    return d_nodeManager->mkDatatypeType(dt);
  }

  std::unique_ptr<PreprocessingPassContext> d_context;
  std::unique_ptr<DtElim> d_pass;
  TypeNode d_int;
  TypeNode d_bool;
  TypeNode d_pair;
};

TEST_F(TestPPWhiteDtElim, functionSignatures)
{
  NodeManager* nm = d_nodeManager.get();
  Node x = nm->mkVar("x", d_pair);
  Node f = nm->mkVar("f", nm->mkFunctionType({d_pair, d_int}, d_pair));
  std::vector<Node> fs = d_pass->convert(f);
  ASSERT_EQ(fs.size(), 2);
  EXPECT_EQ(fs[0].getType(), nm->mkFunctionType({d_int, d_bool, d_int}, d_int));
  EXPECT_EQ(fs[1].getType(),
            nm->mkFunctionType({d_int, d_bool, d_int}, d_bool));
  Node app = nm->mkNode(Kind::APPLY_UF, f, x, nm->mkConstInt(3));
  std::vector<Node> terms = d_pass->convert(app);
  ASSERT_EQ(terms.size(), 2);
  EXPECT_EQ(terms[0].getOperator(), fs[0]);
  EXPECT_EQ(terms[1].getOperator(), fs[1]);
  EXPECT_EQ(terms[0].getNumChildren(), 3);
  EXPECT_EQ(terms[0][0], terms[1][0]);
  EXPECT_EQ(terms[0][1], terms[1][1]);
  EXPECT_EQ(d_pass->convert(x)[0], terms[0][0]);
  EXPECT_EQ(d_pass->convert(x)[1], terms[0][1]);
  EXPECT_NE(d_pass->convert(nm->mkVar("y", d_pair))[0], terms[0][0]);
}

TEST_F(TestPPWhiteDtElim, emptyAndNestedProducts)
{
  NodeManager* nm = d_nodeManager.get();
  TypeNode unit = product("Unit", {});
  TypeNode nested = product("Nested", {unit, d_pair, unit});
  EXPECT_EQ(d_pass->convertType(nested),
            (std::vector<TypeNode>{d_int, d_bool}));
  Node u = nm->mkVar("u", unit);
  Node f = nm->mkVar("f", nm->mkFunctionType({unit}, d_pair));
  const std::vector<Node>& fs = d_pass->convert(f);
  ASSERT_EQ(fs.size(), 2);
  EXPECT_EQ(fs[0].getType(), d_int);
  EXPECT_EQ(fs[1].getType(), d_bool);
  EXPECT_EQ(d_pass->convert(nm->mkNode(Kind::APPLY_UF, f, u)), fs);
  Node g = nm->mkVar("g", nm->mkFunctionType({d_pair}, unit));
  EXPECT_TRUE(d_pass->convert(g).empty());
  Node v = nm->mkVar("v", unit);
  EXPECT_EQ(d_pass->convert(u.eqNode(v))[0], nm->mkConst(true));
  Node distinct = d_pass->convert(nm->mkNode(Kind::DISTINCT, u, v))[0];
  EXPECT_EQ(d_slvEngine->getEnv().getRewriter()->rewrite(distinct),
            nm->mkConst(false));
}

TEST_F(TestPPWhiteDtElim, functionValuedField)
{
  NodeManager* nm = d_nodeManager.get();
  TypeNode field = nm->mkFunctionType({d_int}, d_bool);
  TypeNode dt = product("FunctionBox", {field});
  Node f = nm->mkVar("f", nm->mkFunctionType({d_int}, dt));
  Node app = nm->mkNode(Kind::APPLY_UF, f, nm->mkConstInt(0));
  const std::vector<Node>& result = d_pass->convert(app);
  ASSERT_EQ(result.size(), 1);
  EXPECT_EQ(result[0].getType(true), field);
  EXPECT_EQ(result[0].getKind(), Kind::HO_APPLY);
}

TEST_F(TestPPWhiteDtElim, parametricProducts)
{
  NodeManager* nm = d_nodeManager.get();
  TypeNode param = nm->mkSort("T");
  DType dt("Box", {param});
  auto c = std::make_shared<DTypeConstructor>("box");
  c->addArg("value", param);
  dt.addConstructor(c);
  TypeNode box = nm->mkDatatypeType(dt);
  TypeNode bp = box.instantiate({d_pair});
  EXPECT_EQ(d_pass->convertType(bp), (std::vector<TypeNode>{d_int, d_bool}));
  EXPECT_EQ(d_pass->convertType(box.instantiate({d_int})),
            (std::vector<TypeNode>{d_int}));
}

TEST_F(TestPPWhiteDtElim, recursiveConstructorFields)
{
  NodeManager* nm = d_nodeManager.get();
  TypeNode up = nm->mkUnresolvedDatatypeSort("P");
  TypeNode ul = nm->mkUnresolvedDatatypeSort("L");
  DType p("P");
  auto pc = std::make_shared<DTypeConstructor>("pair");
  pc->addArg("first", d_int);
  pc->addArg("rest", ul);
  p.addConstructor(pc);
  DType l("L");
  l.addConstructor(std::make_shared<DTypeConstructor>("nil"));
  auto lc = std::make_shared<DTypeConstructor>("cons");
  lc->addArg("head", up);
  l.addConstructor(lc);
  std::vector<TypeNode> orig = nm->mkMutualDatatypeTypes({p, l});
  std::vector<TypeNode> ps = d_pass->convertType(orig[0]);
  ASSERT_EQ(ps.size(), 2);
  EXPECT_EQ(ps[0], d_int);
  TypeNode newList = ps[1];
  EXPECT_NE(newList, orig[1]);
  EXPECT_EQ(d_pass->convertType(orig[1]), (std::vector<TypeNode>{newList}));
  ASSERT_EQ(newList.getDType().getNumConstructors(), 2);
  const DTypeConstructor& cons = newList.getDType()[1];
  ASSERT_EQ(cons.getNumArgs(), 2);
  EXPECT_EQ(cons.getArgType(0), d_int);
  EXPECT_EQ(cons.getArgType(1), newList);
  // Reprocessing generated types must be idempotent.
  EXPECT_EQ(d_pass->convertType(newList), (std::vector<TypeNode>{newList}));
}

TEST_F(TestPPWhiteDtElim, bindersAndSelectors)
{
  NodeManager* nm = d_nodeManager.get();
  Node x = NodeManager::mkBoundVar(d_pair);
  Node y = NodeManager::mkBoundVar(d_pair);
  Node eq = x.eqNode(y);
  Node inner =
      nm->mkNode(Kind::EXISTS, nm->mkNode(Kind::BOUND_VAR_LIST, y), eq);
  Node q = nm->mkNode(Kind::FORALL, nm->mkNode(Kind::BOUND_VAR_LIST, x), inner);
  Node result = d_pass->convert(q)[0];
  ASSERT_EQ(result.getKind(), Kind::FORALL);
  ASSERT_EQ(result[0].getNumChildren(), 2);
  EXPECT_EQ(result[0][0].getType(), d_int);
  EXPECT_EQ(result[0][1].getType(), d_bool);
  EXPECT_FALSE(expr::hasFreeVar(result));
  Node sel = nm->mkNode(
      Kind::APPLY_SELECTOR, d_pair.getDType()[0][1].getSelector(), x);
  EXPECT_EQ(d_pass->convert(sel)[0], result[0][1]);
  Node lam = nm->mkNode(Kind::LAMBDA, nm->mkNode(Kind::BOUND_VAR_LIST, x), x);
  const std::vector<Node>& ls = d_pass->convert(lam);
  ASSERT_EQ(ls.size(), 2);
  EXPECT_EQ(ls[0].getType(), nm->mkFunctionType({d_int, d_bool}, d_int));
  EXPECT_EQ(ls[1].getType(), nm->mkFunctionType({d_int, d_bool}, d_bool));
  EXPECT_FALSE(expr::hasFreeVar(ls[0]));
  EXPECT_FALSE(expr::hasFreeVar(ls[1]));
}

TEST_F(TestPPWhiteDtElim, annotations)
{
  NodeManager* nm = d_nodeManager.get();
  Node x = NodeManager::mkBoundVar(d_int);
  Node a = nm->mkVar("a", d_pair);
  Node p = nm->mkVar("p", nm->mkFunctionType({d_int}, d_bool));
  Node f = nm->mkVar("f", nm->mkFunctionType({d_int, d_pair}, d_bool));
  Node pattern =
      nm->mkNode(Kind::INST_PATTERN, nm->mkNode(Kind::APPLY_UF, f, x, a));
  Node q = nm->mkNode(Kind::FORALL,
                      nm->mkNode(Kind::BOUND_VAR_LIST, x),
                      nm->mkNode(Kind::APPLY_UF, p, x),
                      nm->mkNode(Kind::INST_PATTERN_LIST, pattern));
  // Symbols that occur only in patterns must also be translated, even when
  // the body and bound variables do not change.
  Node result = d_pass->convert(q)[0];
  ASSERT_EQ(result.getNumChildren(), 3);
  EXPECT_EQ(result[0], q[0]);
  EXPECT_EQ(result[1], q[1]);
  Node translated = result[2][0][0];
  EXPECT_EQ(translated.getOperator(), d_pass->convert(f)[0]);
  ASSERT_EQ(translated.getNumChildren(), 3);
  EXPECT_EQ(translated[0], x);
  EXPECT_EQ(translated[1], d_pass->convert(a)[0]);
  EXPECT_EQ(translated[2], d_pass->convert(a)[1]);
  EXPECT_EQ(result.getType(true), d_bool);
}

TEST_F(TestPPWhiteDtElim, patternGroupsAndAttributes)
{
  NodeManager* nm = d_nodeManager.get();
  Node x = NodeManager::mkBoundVar(d_pair);
  Node f = nm->mkVar("f", nm->mkFunctionType({d_pair}, d_pair));
  Node g = nm->mkVar("g", nm->mkFunctionType({d_pair}, d_bool));
  Node fx = nm->mkNode(Kind::APPLY_UF, f, x);
  Node gx = nm->mkNode(Kind::APPLY_UF, g, x);
  Node qid = nm->mkNode(Kind::INST_ATTRIBUTE,
                        nm->mkConst(String("qid")),
                        nm->mkVar("product_quantifier", d_bool));
  Node patterns = nm->mkNode(Kind::INST_PATTERN_LIST,
                             {nm->mkNode(Kind::INST_PATTERN, fx, gx),
                              nm->mkNode(Kind::INST_PATTERN, fx),
                              nm->mkNode(Kind::INST_NO_PATTERN, fx),
                              qid});
  for (Kind k : {Kind::FORALL, Kind::EXISTS})
  {
    Node q = nm->mkNode(
        k, nm->mkNode(Kind::BOUND_VAR_LIST, x), fx.eqNode(x), patterns);
    Node result = d_pass->convert(q)[0];
    ASSERT_EQ(result.getNumChildren(), 3);
    ASSERT_EQ(result[0].getNumChildren(), 2);
    EXPECT_EQ(result[0][0], d_pass->convert(x)[0]);
    EXPECT_EQ(result[0][1], d_pass->convert(x)[1]);
    const std::vector<Node>& fs = d_pass->convert(fx);
    Node gs = d_pass->convert(gx)[0];
    ASSERT_EQ(result[2].getNumChildren(), 5);
    EXPECT_EQ(result[2][0], nm->mkNode(Kind::INST_PATTERN, fs[0], fs[1], gs));
    EXPECT_EQ(result[2][1], nm->mkNode(Kind::INST_PATTERN, fs[0], fs[1]));
    EXPECT_EQ(result[2][2], nm->mkNode(Kind::INST_NO_PATTERN, fs[0]));
    EXPECT_EQ(result[2][3], nm->mkNode(Kind::INST_NO_PATTERN, fs[1]));
    EXPECT_EQ(result[2][4], qid);
    EXPECT_EQ(result.getType(true), d_bool);
    EXPECT_FALSE(expr::hasFreeVar(result));
    EXPECT_EQ(d_pass->convert(result)[0], result);
  }
}

TEST_F(TestPPWhiteDtElim, unchangedAnnotations)
{
  NodeManager* nm = d_nodeManager.get();
  Node x = NodeManager::mkBoundVar(d_int);
  Node f = nm->mkVar("f", nm->mkFunctionType({d_int}, d_bool));
  Node fx = nm->mkNode(Kind::APPLY_UF, f, x);
  Node patterns =
      nm->mkNode(Kind::INST_PATTERN_LIST, nm->mkNode(Kind::INST_PATTERN, fx));
  Node q = nm->mkNode(
      Kind::FORALL, nm->mkNode(Kind::BOUND_VAR_LIST, x), fx, patterns);
  EXPECT_EQ(d_pass->convert(q)[0], q);
}

TEST_F(TestPPWhiteDtElim, emptyPatterns)
{
  NodeManager* nm = d_nodeManager.get();
  TypeNode unit = product("Unit", {});
  Node x = NodeManager::mkBoundVar(d_int);
  Node f = nm->mkVar("f", nm->mkFunctionType({d_int}, unit));
  Node p = nm->mkVar("p", nm->mkFunctionType({d_int}, d_bool));
  Node fx = nm->mkNode(Kind::APPLY_UF, f, x);
  Node px = nm->mkNode(Kind::APPLY_UF, p, x);
  Node patterns = nm->mkNode(Kind::INST_PATTERN_LIST,
                             nm->mkNode(Kind::INST_PATTERN, fx),
                             nm->mkNode(Kind::INST_NO_PATTERN, fx));
  Node bvl = nm->mkNode(Kind::BOUND_VAR_LIST, x);
  Node q = nm->mkNode(Kind::FORALL, bvl, px, patterns);
  Node result = d_pass->convert(q)[0];
  EXPECT_EQ(result, nm->mkNode(Kind::FORALL, bvl, px));
  EXPECT_EQ(result.getType(true), d_bool);
  // Removing an empty term must retain the other terms in its multi-pattern.
  patterns = nm->mkNode(Kind::INST_PATTERN_LIST,
                        nm->mkNode(Kind::INST_PATTERN, fx, px));
  result = d_pass->convert(nm->mkNode(Kind::FORALL, bvl, px, patterns))[0];
  ASSERT_EQ(result.getNumChildren(), 3);
  EXPECT_EQ(result[2][0], nm->mkNode(Kind::INST_PATTERN, px));
  EXPECT_EQ(result.getType(true), d_bool);
}

TEST_F(TestPPWhiteDtElim, unsupportedContainers)
{
  NodeManager* nm = d_nodeManager.get();
  for (TypeNode t : {nm->mkArrayType(d_int, d_pair),
                     nm->mkArrayType(d_pair, d_int),
                     nm->mkSetType(d_pair),
                     nm->mkBagType(d_pair),
                     nm->mkSequenceType(d_pair)})
  {
    EXPECT_THROW(d_pass->convertType(t), LogicException);
  }
  TypeNode a = nm->mkArrayType(d_int, d_bool);
  EXPECT_EQ(d_pass->convertType(a), (std::vector<TypeNode>{a}));
  // Containers as fields are fine when the contained types do not change.
  TypeNode p = product("ArrayField", {a, d_int});
  EXPECT_EQ(d_pass->convertType(p), (std::vector<TypeNode>{a, d_int}));
  // A single component still changes representation and must be rejected.
  TypeNode one = product("One", {d_int});
  EXPECT_THROW(d_pass->convertType(nm->mkSetType(one)), LogicException);
}

TEST_F(TestPPWhiteDtElim, unsupportedCodatatype)
{
  DType dt("Stream", true);
  auto c = std::make_shared<DTypeConstructor>("stream");
  c->addArg("head", d_int);
  c->addArgSelf("tail");
  dt.addConstructor(c);
  EXPECT_THROW(d_pass->convertType(d_nodeManager->mkDatatypeType(dt)),
               LogicException);
}

}  // namespace test
}  // namespace cvc5::internal
