/* Declarations added by the port of theory_arith_core; included inside
 * the body of class TheoryArith (protected). */

/**
 * mk_idiv_mod_axioms and mk_div_axiom, for the given flavor of the operators.
 * Z3 rebuilds div/mod terms from their arguments; cvc5 has a partial and a
 * total version of each, so the axioms must be stated over the one that
 * occurs in the input. The two-argument versions use the total operators.
 */
void mkIdivModAxioms(TNode dividend, TNode divisor, bool total);
void mkDivAxiom(TNode dividend, TNode divisor, bool total);

/**
 * The value Z3's mk_value gives the variable of n: the rational part plus
 * d_epsilon times the infinitesimal part, truncated for an integer variable.
 * The caller computes d_epsilon (computeEpsilon, refineEpsilon) first, as
 * Z3's init_model does unless d_modelDependsOnComputedEpsilon.
 */
bool getModelValue(ENode* n, Node& r);
