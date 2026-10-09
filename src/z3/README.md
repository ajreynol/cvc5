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
| `push_app_ite.{h,cpp}` | `ast/rewriter/push_app_ite.*` |
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

   **Levels are not stable under instantiation, and the core depends on them
   being normalized.** Z3 gets this for free: its de Bruijn indices are
   relative, so when it instantiates a quantifier whose body holds another
   one, the inner variables shift down by themselves. Levels are absolute, so
   a nested quantifier arrives at the core still numbered from the enclosing
   scope -- variable level 1 in a quantifier that has one declaration -- and
   everything that indexes per-quantifier state by variable level reads the
   wrong slot: the pattern compiler's `d_vars`, the inverted path index's
   `d_varPaths`, the checker's bindings. The invariant is restored by
   renormalizing every instance in `SmtContext::internalizeInstance`, which is
   idempotent on the parts that are already canonical. Nested quantifiers are
   not a corner case in the benchmark set -- the requires/ensures axiom of
   every Verus function is one -- and before this was fixed the port solved
   210 of the 300-benchmark sample rather than the figure below.

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

   **Only those parts.** Z3's default mode is `NNF_SKOLEM`, whose `visit()`
   leaves a quantifier-free subformula exactly as it found it; the comment
   there, "this mode is sufficient when using E-matching", is the reason. A
   port that converts the whole formula is not just doing extra work: pushing
   negations through ground structure duplicates every subformula needed in
   both polarities, which gave the core 2.3 times the Boolean variables and 7
   times the binary clauses Z3 builds, and a correspondingly worse search.
   Restricting the conversion to subformulas with a closure, and matching
   Z3's `process_ite` shape rather than pushing the negation outwards, took
   the 300-benchmark sample from 262 solved to 275.
2. **Top-level conjunctions are split into separate assertions.**
   `asserted_formulas::push_assertion` splits them; `SmtContext::pushAssertion`
   does the same. This is not an optimization: an assertion is marked relevant
   when it is asserted, while the conjuncts of a top-level conjunction never
   are, because the and-gate only propagates relevancy once the conjunction
   itself is assigned, which never happens for a root. Leaving them unsplit
   starves E-matching of candidates -- on one UFDT benchmark it was the
   difference between 142 and 7186 candidate enodes. `pushAssertion` also
   does the job of Z3's `flatten_clauses`, turning a top-level if-then-else
   into its two clauses and distributing a disjunction over a conjunction
   when the other side is a literal, so that the core gets flat clauses
   rather than a tree of gates.

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

  A third thing is needed to keep the interface equalities under control.
  Z3's arithmetic solver calls `random_update` before it assumes any equality,
  which perturbs the shared variables that have slack so that only the ones
  genuinely pinned together keep equal values. Reading a subsolver's model
  instead gives whatever value it happened to pick -- typically zero for
  everything unconstrained -- so every coincidence looks like an equality
  worth deciding: on one benchmark the core was handed 39034 of them where Z3
  assumes 30. `separateSharedValues` asks the subsolver for a model that keeps
  the coinciding groups apart, one query for all the groups and then one per
  group if that fails, which brought the same benchmark to 32 and its runtime
  from 24s to 9s. (The abstractions have to be deduplicated first: two
  congruence roots can abstract to the same term, and asking *those* to differ
  is unsatisfiable for a reason that has nothing to do with arithmetic.)

  What this does *not* reproduce is the eager equality propagation of Z3's
  simplex, which merges congruence classes in the middle of the search and so
  feeds E-matching. Two attempts at it are implemented and both default to
  off. Running the bridge during propagation as well (`--z3-bridge-eager`)
  loses more than it gains, because one subsolver call costs far more than one
  simplex step. Asking the subsolver which shared terms are *pinned* to their
  value and propagating those equalities (`--z3-bridge-fixed-eqs`) is the
  closer analogue -- Z3 propagates thousands of them, and the merge is what
  creates the numeral's enode, without which a pattern like `(Add 8 0)` can
  never match -- but each group costs a query, and measured on one benchmark
  it bought nineteen merges for five seconds. This is the clearest remaining
  structural gap in the bridge: the information is cheap inside a simplex and
  expensive through an assumption interface. Making the bridge mirror the
  core's scopes with push/pop, asserting literals as they are assigned instead
  of resending them, is the change that would make these queries affordable.

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
| z3 | 289 | 0 | 11 | 168s |
| cvc5 | 274 | 0 | 26 | 434s |
| cvc5 `--z3` | 276 | 14 | 10 | 232s |

**The cvc5 baseline is `cvc5 --user-pat=strict --no-cbqi`.** The cvc5 row
above did not record its options, so it should not be read as the baseline;
it is to be re-measured. Every comparison from now
on includes cvc5 with exactly those two options.

Of the 289 the two solvers between them close, `--z3` closes 276 and cvc5
itself 274, in a little over half cvc5's time. No answer of any of the three
contradicts another on this sample, and `ctest -R regress0` is clean.

The port started this work at 106 solved and reached 210 with the datatypes
plugin, the two preprocessing invariants above, the default quantifier weight
and the Nelson-Oppen abstraction in the theory bridge. Four findings took it
from there to 276, and all four were the same kind of mistake -- a mechanism
of Z3 that looked optional and was not:

1. **Levels are not stable under instantiation** (the de Bruijn note above).
   210 -> 262. Nested quantifiers are not a corner case here; the
   requires/ensures axiom of every Verus function is one.
2. **NNF applies only to subformulas that hold a quantifier**, which is Z3's
   `NNF_SKOLEM` mode, and a negated if-then-else keeps its shape. 262 -> 275.
3. **`random_update` before assuming interface equalities.** 39034 case splits
   became 32 on the benchmark it was measured on, and one benchmark went from
   24s to 9s. 275 -> 276, and several of the remaining timeouts moved from
   "does not finish" to "finishes just over the limit".
4. **`setup_unknown` picks `setup_AUFLIA(false)`, not its static-feature
   overload**, so the eager instantiation threshold for these logics is Z3's
   default 10 rather than 7. This turned out to make no difference at all, and
   the reason is worth recording: `qi_queue::setup` copies the threshold into
   `m_eager_cost_threshold` from the `quantifier_manager`'s constructor, which
   runs before `setup_context` has adjusted any parameter, so in Z3 every
   logic's override of `m_qi_eager_threshold` is dead. The port creates its
   `QuantifierManager` in `SmtContext`'s constructor for the same reason and
   inherits the same behaviour.

One faithful reproduction of Z3 is deliberately *not* the default.
`asserted_formulas::reduce()` calls `set_eliminate_and(true)` once NNF is
done, so Z3's core never sees a conjunction -- every `(and a b)` is
`(not (or (not a) (not b)))`. Doing the same (`--z3-eliminate-and`) behaves
exactly as it should on the formula examined most closely: decisions fall from
3469 to 2856 against Z3's 2590, Boolean variables from 7406 to 7076, instances
from 2171 to 2049. Over the whole sample it costs nine solved benchmarks.
Something downstream is tuned to the conjunctions being there; until that is
found the measurement wins, and the option records where to look.

The 14 remaining `unknown` answers are all the same thing: E-matching
saturates, and with no model based instantiation there is nothing to pick the
next binding with. They are not a speed problem -- raising the limit converts
none of them. Dumping the saturated state and asking cvc5 shows it is
genuinely refutable, and giving Z3 the port's own formula shows Z3 closing it
with a quarter of the instantiations the port makes, so what is missing is not
coverage of the matching but the search reaching the state where the matching
pays off. The instances Z3 has and the port never produces are, on the
benchmark examined most closely, arithmetic ones -- `(Add 8 0)`, `(uInv 32 0)`
-- whose triggers only exist once a term has been merged with a numeral, which
brings it back to the equality propagation the bridge cannot afford.

The 10 remaining timeouts are a different matter: every one of them is solved,
just not inside 10 seconds. They run 4x to 30x slower than Z3 does, and where
the time goes is measurable -- on the arithmetic-heavy ones 60% to 90% of it
is inside the theory bridge's subsolver.

## Comparing a run against Z3's

The differential method that found most of the bugs above needs the two
solvers to be looking at the *same* formula, which they are not by default:
this port runs cvc5's preprocessor and then its own. These expert options
exist for that:

- `--z3-dump-assertions=FILE` writes what the core is given, after the whole
  pipeline, as a parsable benchmark. Running Z3 on that file removes
  preprocessing from the comparison entirely -- on one UFDTLIA query Z3 closed
  the port's own formula with 576 instantiations where the port made 2171 and
  still saturated, which is a statement about the search and nothing else.
- `--z3-dump-instances=FILE` writes every instance the core creates, one per
  line, in the form Z3's `-tr:qi_queue` prints as "new instance". Z3 needs
  `pp.min_alias_size=1000000 pp.max_width=100000000` to stop abbreviating with
  `let`, and the bound variable names agree because both read them from the
  same file, so the two sets can be diffed directly.
- `--z3-qi-profile` prints the per-quantifier counts Z3's `smt.qi.profile=true`
  prints, with each quantifier's patterns appended -- Z3 identifies them by
  `qid`, which these benchmarks do not set, and the patterns line up across
  solvers where a generated name does not.
- `--z3-dump-saturated=FILE` writes the state E-matching saturated in: the
  assigned relevant ground literals together with every quantified assertion.
  If cvc5 reports that file unsat, saturation was premature, and
  `--dump-instantiations` names instances that would have closed it.
- `--z3-check-saturated` hands just the ground literals to a full cvc5
  subsolver. "sat" means the ground reasoning is consistent and a quantifier
  instance is missing; "unsat" means a theory of the port is too weak.

## Known performance differences

Two separate things, measured on a hard crafted QF_UF benchmark run through
cvc5's preprocessor so that both solvers get the identical formula:

1. **Search quality.** The port needs about 3.4x the conflicts Z3 does
   (123k vs 36k) in its best configuration. Everything *per* conflict matches
   Z3 closely -- propagations per conflict 28 vs 24, added equalities per
   conflict 170 vs 166, minimized literals per conflict 11.5 vs 9.7 -- so the
   difference is in which conflicts the search finds, not in the cost of
   finding them. The heuristics were audited against Z3 line by line
   (`guess`, `updatePhaseCacheCounter`, `assignCore`'s phase saving,
   `delInactiveLemmas1`, activity bumping and decay, the random variable
   frequency) and all agree, so whatever is left is subtler than a missing
   rule. One concrete symptom worth starting from: `PS_CACHING_CONSERVATIVE2`,
   the phase selection `setup_QF_UF` chooses, costs the port 2.8x against its
   own default while it costs Z3 only 1.25x, which suggests the phase cache is
   not behaving the same way even though the code reads the same.
2. **Constant factor.** With the search work held equal the port is about 1.4x
   slower per unit of work. The congruence table is the first suspect: it is
   backed by `std::unordered_set`, which chains and allocates a node per
   element, where Z3 uses its own open-addressing `chashtable`.

Neither is what limits `--z3` on the benchmark set above -- the 14 unknown
answers are -- but both would have to go to claim parity.

Run with `--stats-all` to get the core's own counters (`z3::conflicts`,
`z3::decisions`, `z3::propagations`, `z3::addEq`, ...), which are named to line
up with Z3's `-st` output so that the two searches can be compared directly.
