# A port of Z3's SMT core into cvc5

This directory contains a port of Z3's `smt::context` and the machinery around
it, exposed through the `--z3` option. The purpose is experimental: to measure
how much of Z3's quantifier performance is reproducible inside cvc5, by
replicating the algorithms that produce it rather than approximating them.

Enabling `--z3` replaces cvc5's CDCL(T) engine. Everything else stays cvc5's:
the parser, the term representation (`Node`), the rewriter, and the
preprocessor. `smt::Z3SmtSolver` takes the output of cvc5's `Preprocessor`
and, instead of handing it to the `PropEngine`, internalizes it into a
`z3::SmtContext`, which then owns the search.

## Provenance and licensing

The ported files carry a header naming the Z3 file they came from. Z3 is
distributed under the MIT License, Copyright (c) Microsoft Corporation; that
notice is preserved in each ported file. Code that is *not* from Z3 --
`theory_cvc5.*`, `ast.*`, and the `--z3` option plumbing -- says so.

Constants, hash functions and default parameter values are kept bit-for-bit
identical to Z3's, because they are part of what is being replicated. See
`setup.cpp` in particular: with auto configuration on, Z3 solves a quantified
problem with phase selection "always false", geometric restarts with factor
1.5, an eager instantiation threshold of 7, and MBQI enabled, none of which
are the values in `smt_params.h`.

## File map

| cvc5 file | ported from |
|---|---|
| `smt_context.{h,cpp}` | `smt/smt_context.{h,cpp}` |
| `internalizer.cpp` | `smt/smt_internalizer.cpp` |
| `enode.{h,cpp}`, `cg_table.{h,cpp}` | `smt/smt_enode.*`, `smt/smt_cg_table.*` |
| `relevancy.{h,cpp}` | `smt/smt_relevancy.*` |
| `case_split_queue.{h,cpp}` | `smt/smt_case_split_queue.*` |
| `conflict_resolution.{h,cpp}` | `smt/smt_conflict_resolution.*` |
| `clause.{h,cpp}`, `watch_list.{h,cpp}` | `smt/smt_clause.*`, `smt/watch_list.*` |
| `justification.{h,cpp}`, `b_justification.h`, `eq_justification.h` | `smt/smt_justification.*`, `smt/smt_b_justification.h`, `smt/smt_eq_justification.h` |
| `bool_var_data.h`, `statistics.{h,cpp}` | `smt/smt_bool_var_data.h`, `smt/smt_statistics.h` |
| `theory.{h,cpp}` | `smt/smt_theory.*` |
| `dyn_ack.{h,cpp}` | `smt/dyn_ack.*` |
| `fingerprints.{h,cpp}` | `smt/fingerprints.*` |
| `quantifier_manager.{h,cpp}` | `smt/smt_quantifier.*` |
| `qi_queue.{h,cpp}` | `smt/qi_queue.*` |
| `checker.{h,cpp}` | `smt/smt_checker.*` |
| `cost_function.{h,cpp}` | `parsers/util/cost_parser.cpp`, `ast/cost_evaluator.cpp` |
| `quantifier_stat.{h,cpp}` | `ast/quantifier_stat.*` |
| `mam.{h,cpp}` | `smt/mam.*` |
| `setup.{h,cpp}`, `params.{h,cpp}` | `smt/smt_setup.cpp`, `params/smt_params.*`, `params/qi_params.*` |
| `util/*` | the corresponding files in Z3's `src/util` |

## The AST bridge

cvc5's `Node` is the AST; none of Z3's `ast.h` or `ast_manager` is ported.
`ast.h` bridges the two places where Z3's model genuinely differs:

1. **Congruence keys.** Z3 keys congruence closure on `func_decl*`; cvc5
   splits that between the `Kind` and, for parameterized kinds, an operator
   node. `getDecl(n)` recovers a single node that plays the same role.
2. **Quantified variables.** Z3 uses de Bruijn variables and `mam.cpp` binds
   pattern variables by index; cvc5 uses named bound variables, so two
   quantifiers with the same pattern up to renaming would compile to distinct
   code trees and lose all E-matching sharing. `QuantifierNormalizer` rewrites
   each quantifier over a canonical pool of placeholders indexed by de Bruijn
   *level*, which is both alpha-invariant and capture-free. The binding
   convention is that `bindings[i]` is the binding of the `i`-th variable of
   the bound variable list, matching Z3's `bindings[k]` being the binding of
   the `k`-th declared variable.

## What is not ported

Deliberately out of scope, because cvc5 already provides it or it is
irrelevant to the experiment: proof production, the user propagator, parallel
and lookahead search, consequence finding, Z3's `asserted_formulas`
preprocessing pipeline, lambdas, and Z3 label literals.

Not ported *yet*, and therefore limiting what `--z3` can answer today:

- **`mam.cpp`'s code trees.** `mam.cpp` currently accepts patterns but never
  produces a match, so E-matching performs no instantiation.
- **Theory plugins.** `theory_cvc5.cpp` is where cvc5's bit-vector and
  arithmetic solvers are meant to be attached; both factories return null.
  Datatypes have no plugin either.
- **Model based instantiation** (`smt_model_finder.cpp`,
  `smt_model_checker.cpp`) and the **quick checker**
  (`smt_quick_checker.cpp`). Note `setup.cpp` sets `qi_quick_checker` to
  `MC_UNSAT` for quantified problems, as Z3 does, so this is a live behavioral
  difference, not just a missing option.
- Z3's `CS_RELEVANCY_GOAL` case split queue, which tracks the current goal
  through Z3 label literals that cvc5's input language does not produce.
- The "almost congruence" index behind `isExtDiseq`, which exists for array
  extensionality.

**This is arranged to be sound, not silently wrong.** When a term of a theory
with no plugin is internalized, or a pattern is registered that will never
fire, the core calls `SmtContext::markModelUnsound`. Since both situations
*drop* constraints rather than adding them, an "unsat" answer remains sound,
while a satisfying assignment is only an assignment of an abstraction and is
reported as "unknown". So `--z3` will never claim "sat" on a problem it cannot
actually reason about.

## Known performance differences

The congruence table is backed by `std::unordered_set`, which chains and
allocates a node per element, where Z3 uses its own open-addressing
`chashtable`. The table is hot in E-matching-heavy problems, so this is the
first place to look if the port is slower than Z3 by a constant factor.

Run with `--stats-all` to get the core's own counters (`z3::conflicts`,
`z3::decisions`, `z3::propagations`, `z3::addEq`, ...), which are named to line
up with Z3's `-st` output so that the two searches can be compared directly.
