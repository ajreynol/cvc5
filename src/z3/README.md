# The ported Z3 core (`--z3`)

A port of Z3's E-matching core, which runs as the only module of cvc5's
quantifiers engine (`Z3Module`). cvc5's own prop engine and theories do the
ground reasoning, and cvc5's quantifiers engine registers the quantified
formulas and skolemizes those asserted false (the core takes that lemma when
the formula is relevant to it); the core keeps a shadow of the ground state (an E-graph, and a
Boolean mirror of the SAT assignment for Z3's relevancy) and sends quantifier
instances, splits and delayed units to cvc5 as lemmas. Since it sends
only lemmas, it never explains anything, and keeps no justifications.

## Layout and inclusion rules

| Directory | Contents | May include (from the port) |
|---|---|---|
| `src/z3/util/` | 16 | 1458 | 526 | 341 |
| `src/z3/relevancy/` | 12 | 2278 | 521 | 374 |
| `src/z3/quantifiers/` | 27 | 8473 | 1531 | 1047 |
| **Total** | 55 | **12209** | 2578 | 1762 |

The rest of cvc5 changes by 252 added and 11 deleted lines over 16 C++ files,
most of them in `smt/set_defaults.cpp` (the capability checks) and
`theory/quantifiers/quantifiers_preprocess.cpp` (pre-skolemization of
quantified formulas with patterns).
