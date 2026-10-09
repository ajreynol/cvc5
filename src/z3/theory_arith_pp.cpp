/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Printing for the simplex-based arithmetic solver of the ported Z3 core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), file
 * src/smt/theory_arith_pp.h, and recast in cvc5 style. Statistics are
 * collected differently in the port, and the debugging helpers that print
 * row shapes and statistics or bounds in SMT-LIB are not ported.
 */

#include <ostream>

#include "z3/smt_context.h"
#include "z3/theory_arith.h"

namespace cvc5::internal {
namespace z3 {

void TheoryArith::print(std::ostream& out) const
{
  if (getNumVars() == 0)
  {
    return;
  }
  out << "Theory arithmetic:\n";
  printVars(out);
  printNlMonomials(out);
  printRows(out, true);
  printRows(out, false);
  printAtoms(out);
  printAssertedAtoms(out);
}

void TheoryArith::printNlMonomials(std::ostream& out) const
{
  if (d_nlMonomials.empty())
  {
    return;
  }
  out << "non linear monomials:\n";
  for (TheoryVar nl : d_nlMonomials)
  {
    printVar(out, nl);
  }
}

void TheoryArith::printRow(std::ostream& out, size_t rId, bool compact) const
{
  out << rId << " ";
  printRow(out, d_rows[rId], compact);
}

void TheoryArith::printRow(std::ostream& out, const Row& r, bool compact) const
{
  if (static_cast<size_t>(r.getBaseVar()) >= d_columns.size())
  {
    return;
  }
  const Column& c = d_columns[r.getBaseVar()];
  if (c.size() > 0)
  {
    out << "(v" << r.getBaseVar() << " r" << c[0].d_rowId << ") : ";
  }
  bool first = true;
  for (const RowEntry& e : r)
  {
    if (!e.isDead())
    {
      if (first)
      {
        first = false;
      }
      else
      {
        out << " + ";
      }
      TheoryVar s = e.d_var;
      const Numeral& coeff = e.d_coeff;
      if (!coeff.isOne())
      {
        out << coeff << "*";
      }
      if (compact)
      {
        out << "v" << s;
        if (isFixed(s))
        {
          out << ":" << lower(s)->getValue();
        }
      }
      else
      {
        // Z3's enode_pp
        out << getENode(s)->getExpr();
      }
    }
  }
  out << "\n";
}

void TheoryArith::printRows(std::ostream& out, bool compact) const
{
  if (compact)
  {
    out << "rows (compact view):\n";
  }
  else
  {
    out << "rows (expanded view):\n";
  }
  size_t num = d_rows.size();
  for (size_t rId = 0; rId < num; ++rId)
  {
    if (d_rows[rId].d_baseVar != s_nullTheoryVar)
    {
      printRow(out, rId, compact);
    }
  }
}

void TheoryArith::printVar(std::ostream& out, TheoryVar v) const
{
  out << "v";
  out.width(4);
  out << std::left << v;
  out << " #";
  out.width(4);
  out << getENode(v)->getOwnerId();
  out << std::right;
  out << " lo:";
  out.width(10);
  if (lower(v))
  {
    out << lower(v)->getValue();
  }
  else
  {
    out << "-oo";
  }
  out << ", up:";
  out.width(10);
  if (upper(v))
  {
    out << upper(v)->getValue();
  }
  else
  {
    out << "oo";
  }
  out << ", value: ";
  out.width(10);
  out << getValue(v);
  out << ", occs: ";
  out.width(4);
  out << d_columns[v].size();
  out << ", atoms: ";
  out.width(4);
  out << d_varOccs[v].size();
  out << (isInt(v) ? ", int " : ", real");
  switch (getVarKind(v))
  {
    case NON_BASE: out << ", non-base  "; break;
    case QUASI_BASE: out << ", quasi-base"; break;
    case BASE: out << ", base      "; break;
  }
  out << ", shared: " << d_ctx.isShared(getENode(v));
  out << ", unassigned: " << d_unassignedAtoms[v];
  out << ", rel: " << d_ctx.isRelevant(getENode(v));
  // Z3's enode_pp
  out << ", def: " << getENode(v)->getExpr();
  out << "\n";
}

void TheoryArith::printVars(std::ostream& out) const
{
  out << "vars:\n";
  int n = static_cast<int>(getNumVars());
  int infVars = 0;
  int intInfVars = 0;
  for (TheoryVar v = 0; v < n; ++v)
  {
    if ((lower(v) && lower(v)->getValue() > getValue(v))
        || (upper(v) && upper(v)->getValue() < getValue(v)))
    {
      infVars++;
    }
    if (isInt(v) && !getValue(v).isInt())
    {
      intInfVars++;
    }
  }
  out << "infeasibles = " << infVars << " int_inf = " << intInfVars
      << std::endl;
  for (TheoryVar v = 0; v < n; ++v)
  {
    printVar(out, v);
  }
}

void TheoryArith::printBound(std::ostream& out, Bound* b, size_t indent) const
{
  for (size_t i = 0; i < indent; ++i)
  {
    out << "  ";
  }
  b->print(*this, out);
  out << "\n";
}

void TheoryArith::printAtoms(std::ostream& out) const
{
  out << "atoms:\n";
  for (Atom* a : d_atoms)
  {
    printAtom(out, a, false);
  }
}

void TheoryArith::printAssertedAtoms(std::ostream& out) const
{
  out << "asserted atoms:\n";
  for (size_t i = 0; i < d_assertedQhead; ++i)
  {
    Bound* b = d_assertedBounds[i];
    if (b->isAtom())
    {
      printAtom(out, static_cast<Atom*>(b), true);
    }
  }
  if (d_assertedQhead < d_assertedBounds.size())
  {
    out << "delayed atoms:\n";
    for (size_t i = d_assertedQhead; i < d_assertedBounds.size(); ++i)
    {
      Bound* b = d_assertedBounds[i];
      if (b->isAtom())
      {
        printAtom(out, static_cast<Atom*>(b), true);
      }
    }
  }
}

void TheoryArith::printAtom(std::ostream& out, Atom* a, bool showSign) const
{
  TheoryVar v = a->getVar();
  const InfNumeral& k = a->getK();
  ENode* e = getENode(v);
  if (showSign)
  {
    out << (a->isTrue() ? "    " : "not ");
  }
  out << "v";
  out.width(3);
  out << std::left << v << " #";
  out.width(3);
  out << e->getOwnerId();
  out << std::right;
  out << " " << ((a->getAtomKind() == A_LOWER) ? ">=" : "<=") << " ";
  out.width(6);
  // Z3's enode_pp
  out << k << "    " << getENode(v)->getExpr() << "\n";
}

}  // namespace z3
}  // namespace cvc5::internal
