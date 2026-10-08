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
| `quick_checker.{h,cpp}` | `smt/smt_quick_checker.*` |
| `theory_datatype.{h,cpp}` | `smt/theory_datatype.*` |
| `pattern_inference.{h,cpp}` | `ast/pattern/pattern_inference.*` |
| `setup.{h,cpp}`, `params.{h,cpp}` | `smt/smt_setup.cpp`, `params/smt_params.*`, `params/qi_params.*`, `params/pattern_inference_params.*` |
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

## The preprocessing Z3 does and cvc5 does not

The core inherits two invariants from Z3's own preprocessing pipeline
(`asserted_formulas::reduce()`), which cvc5's preprocessor does not establish.
Both are restored before anything reaches the core, in
`smt::Z3SmtSolver::assertToInternal`:

1. **Universal quantifiers occur only positively.** A Boolean variable of a
   quantifier assigned false is simply ignored, in Z3 and here alike -- see
   the comment in `SmtContext::assignQuantifier`. Z3 establishes this with its
   `nnf` pass; `nnf.{h,cpp}` does the same here, rewriting only the parts of a
   formula that contain a quantifier and skolemizing the existentials. Without
   it the negated goal of a verification query carries no information at all
   and the core answers "unknown" on nearly everything.
2. **Top-level conjunctions are split into separate assertions.**
   `asserted_formulas::push_assertion` splits them; `SmtContext::pushAssertion`
   does the same. This is not an optimization: an assertion is marked relevant
   when it is asserted, while the conjuncts of a top-level conjunction never
   are, because the and-gate only propagates relevancy once the conjunction
   itself is assigned, which never happens for a root. Leaving them unsplit
   starves E-matching of candidates -- on one UFDT benchmark it was the
   difference between 142 and 7186 candidate enodes.

`pattern_inference.{h,cpp}` is the third piece of Z3's pipeline that had to
come along: cvc5 selects triggers inside its quantifiers module rather than
annotating the formula, so a quantifier without a `:pattern` would reach the
core with no trigger at all.

Two details of Z3's AST that the port has to reproduce because the search
depends on them numerically:

- **The default quantifier weight is 1, not 0.** The instance cost is
  `weight + generation` and the generation of the enodes an instance creates
  is its cost, so with weight 0 every instance has cost 0, the generation
  never grows and matching loops are never broken. Z3's `qi_params.h` has a
  long comment about this exact bug. cvc5's parser drops `:weight`, so
  `z3::getWeight` supplies Z3's default.
- `:qid` and `:pattern` annotations survive cvc5's parser and are read
  directly off the `INST_PATTERN_LIST`.

## What is not ported

Deliberately out of scope, because cvc5 already provides it or it is
irrelevant to the experiment: proof production, the user propagator, parallel
and lookahead search, consequence finding, Z3's `asserted_formulas`
preprocessing pipeline, lambdas, and Z3 label literals.

Not ported, and therefore limiting what `--z3` can answer today:

- **Model based quantifier instantiation** (`smt_model_finder.cpp`,
  `smt_model_checker.cpp`). This is the largest remaining gap, and it is not
  only about answering "sat": Z3's model checker is also a *refutation*
  mechanism. When E-matching runs out of matches, it finds a binding the
  candidate model falsifies, adds the instance and restarts the search, which
  is how Z3 reaches instantiation generations the port cannot. Porting it
  faithfully means porting Z3's model construction stack as well -- proto
  models, value factories and the model evaluator -- so it was left out.
  `enum_inst.{h,cpp}` is an attempt at a cheap substitute, using the
  mechanism cvc5 uses for the same purpose; measured over the benchmark set it
  does not pay for itself, so `--z3-enum-inst` defaults to off.
  Consequence: with quantifiers present, a satisfiable problem is always
  reported as "unknown", since `QuantifierManager::checkModel` cannot confirm
  a candidate model.
- Z3's `CS_RELEVANCY_GOAL` case split queue, which tracks the current goal
  through Z3 label literals that cvc5's input language does not produce.
- The "almost congruence" index behind `isExtDiseq`, which exists for array
  extensionality.
- Z3's subterm predicate in the datatypes theory, which cvc5 has no
  counterpart for, and the occurs check through arrays, sequences and sets. A
  datatype that nests one of those over a datatype marks the search
  model-unsound rather than risking a missed cycle.

## The theories

Following the instruction to reuse cvc5's own solvers where they exist:

- **Uninterpreted functions and equality** are the core's own congruence
  closure (`enode.*`, `cg_table.*`), as in Z3.
- **Datatypes** are a port of Z3's `theory_datatype`, which plugs straight
  into the ported `z3::Theory` interface.
- **Arithmetic and bit-vectors** go through `theory_cvc5.{h,cpp}`, which is
  not from Z3. It is a Nelson-Oppen style bridge: the core owns the Boolean
  structure, the equalities and the instantiation, and at each final check the
  assigned arithmetic and bit-vector literals are handed to a cvc5 subsolver
  as assumptions. An unsat answer comes back as the unsat assumptions, which
  become a conflict over literals the core already has; a sat answer is
  followed by interface equality reconciliation, where a pair of shared
  classes the subsolver's model identifies is either propagated as an equality
  (if the subsolver confirms it is entailed) or split on.

  Two things make this affordable. The literals are *abstracted* before they
  are sent: the arithmetic and bit-vector structure is kept and every other
  subterm becomes a fresh constant of the same sort, with the congruence
  closure relating the constants through the interface equalities. Without
  that the subsolver re-solves the whole uninterpreted and datatype part of
  the query on every call; with it, the time one benchmark spent in the
  subsolver fell from 19s to 3.4s. The literals the core assigned at its base
  level are asserted to the subsolver once rather than resent, and both
  verdicts are memoized, since the satisfiability of a set of literals does
  not depend on the scope it was judged in.

  What this does *not* reproduce is the eager equality propagation of Z3's
  simplex, which merges congruence classes in the middle of the search and so
  feeds E-matching. Running the bridge during propagation as well is
  implemented (`--z3-bridge-eager`) but defaults to off: one subsolver call
  costs far more than one simplex step, and measured over the benchmark set it
  loses more than it gains.

**This is arranged to be sound, not silently wrong.** When a term of a theory
with no plugin is internalized, or a pattern is registered that will never
fire, the core calls `SmtContext::markModelUnsound`. Since both situations
*drop* constraints rather than adding them, an "unsat" answer remains sound,
while a satisfying assignment is only an assignment of an abstraction and is
reported as "unknown". So `--z3` will never claim "sat" on a problem it cannot
actually reason about.

## Where it stands

Measured on a 300-benchmark sample of `~/benchmarks/quant-07-25` (UFDT(N)IA
and UFBVDT(N)IA verification queries from Verus) with a 10 second limit, all
three solvers answering only `unsat` or `unknown`:

| | solved | unknown | timeout | total time |
|---|---|---|---|---|
| z3 | 289 | 0 | 11 | 169s |
| cvc5 | 273 | 0 | 27 | 439s |
| cvc5 `--z3` | 210 | 65 | 25 | 374s |

No answer of any of the three contradicts another on this sample.

The port began this round of work at 106 solved; the datatypes plugin, the two
preprocessing invariants above, the default quantifier weight and the
Nelson-Oppen abstraction in the theory bridge are what moved it to 210. The
remaining shortfall is dominated by the 65 "unknown" answers rather than by
speed: raising the limit from 10s to 60s converts almost none of them, while
the absence of model based instantiation explains them directly -- the search
reaches a state where E-matching has no match left, and has nothing with
which to pick the next binding.

## Known performance differences

The congruence table is backed by `std::unordered_set`, which chains and
allocates a node per element, where Z3 uses its own open-addressing
`chashtable`. The table is hot in E-matching-heavy problems, so this is the
first place to look if the port is slower than Z3 by a constant factor. On a
pure QF_UF benchmark the port is about 3.5x slower than Z3 with a comparable
number of conflicts, which is the size of this constant factor.

Run with `--stats-all` to get the core's own counters (`z3::conflicts`,
`z3::decisions`, `z3::propagations`, `z3::addEq`, ...), which are named to line
up with Z3's `-st` output so that the two searches can be compared directly.
