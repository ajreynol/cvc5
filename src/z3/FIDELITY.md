# Where `--z3` is and is not faithful to Z3

This port is meant to be a mechanical exercise: do what Z3 does, so that the
numbers are a baseline rather than a new design. This file is the inventory of
where that holds and where it does not, checked against the two source trees
(`~/z3/src` and `src/z3`) rather than from memory. It is the companion to
`README.md`, which explains the port; this one only records divergences.

Measured state at the time of writing, on a 300-benchmark sample of
`~/benchmarks/quant-07-25` with a 10s limit: z3 289 solved, cvc5 274,
`cvc5 --z3` 276.

## Verified faithful

- **Parameters.** All 82 Z3 parameters the port carries have matching
  defaults. Diffed `params/{smt,qi,dyn_ack,pattern_inference,preprocessor}_params.h`
  and the generated `*_params_helper.hpp` defaults against `src/z3/params.h`.
  The handful of apparent mismatches were constructor-set values that agree
  once resolved.
- **Core search.** Watch lists, BCP, FUIP conflict resolution with lemma
  minimization, restarts, lemma GC, phase caching, activity and decay,
  delayed units, `get_closest_var` / `m_new_core2th_eq`, dynamic
  ackermannization.
- **Relevancy.** The dispatch table matches `smt_relevancy.cpp` case for case,
  including `propagate_relevant_or` marking nothing when no argument is true
  yet.
- **E-matching.** MAM code trees and instruction set, the inverted path index,
  the eager/lazy multi-pattern split (`qi_max_eager_multipatterns`, two MAMs,
  `qi_max_lazy_multipattern_matching`), fingerprint dedup (double lookup, root
  storing, scope erase), the qi queue's cost and new-generation functions,
  thresholds, delayed-entry trail, and the final-check composition.
  `smt_checker` is a line-for-line port.
- **Setup.** These logics reach `setup_unknown(st)` and so
  `setup_AUFLIA(false)`, which the port reproduces. Note Z3's per-logic
  overrides of `m_qi_eager_threshold` are dead code in Z3 — `qi_queue::setup`
  copies it from the `quantifier_manager` constructor, which runs before
  `setup_context` adjusts anything. The port creates its `QuantifierManager` in
  `SmtContext`'s constructor and inherits the same behaviour.
- **Non-Z3 additions are inert by default.** `z3QiQuickCheckerConservative` is
  unreachable because `qi_lazy_quick_checker` is true in Z3 and here, so the
  quick checker never runs; `z3EnumInst*` is off; `z3BridgeEager` and
  `z3BridgeFixedEqs` are off.

## Not faithful, and live on this benchmark set

### Arithmetic and bit-vectors — the one non-mechanical divergence

Z3 runs `theory_arith`/`theory_lra` and `theory_bv` inside the core. Per the
instruction to reuse cvc5's solvers, `theory_cvc5.{h,cpp}` is instead a
Nelson-Oppen bridge to a cvc5 subsolver called with assumptions. This is an
architecture substitution, not a port, and it changes the interaction model:

- no eager bound propagation into the core (Z3: 1850 LP bound propagations on
  one benchmark here);
- no fixed-variable equality propagation (Z3: 2358; the port: 0 by default).
  The merge is what creates a numeral's enode, without which a trigger like
  `(Add 8 0)` or `(uInv 32 0)` can never match — these are exactly the
  instances Z3 has that the port never produces;
- `random_update` only approximated, by asking the subsolver for a model that
  separates the coinciding shared terms (`separateSharedValues`);
- no nlsat. Z3 closes the NIA family with 292 nlsat conflicts in 0.03s; cvc5's
  integer NIA with `nl-cov` disabled does not;
- a per-call resource limit (`--z3-bridge-rlimit-per`) with no Z3 analogue is
  needed, because otherwise a single subsolver call never returns.

60–90% of the runtime on the arithmetic-heavy benchmarks is inside the bridge.
Making it mirror the core's scopes with push/pop, asserting literals as they
are assigned instead of resending assumptions, is the change that would make
the missing propagation affordable.

### Preprocessing — Z3's `asserted_formulas::reduce()`

The port runs cvc5's Preprocessor (per instruction) and then three of Z3's own
passes: `nnf`, `pattern_inference`, and half of `flatten_clauses`. Passes that
are on by default — or that `setup_AUFLIA` turns on for exactly these logics —
and have no port equivalent:

| pass | default | status |
|---|---|---|
| `m_reduce_asserted_formulas` | on | **done** — `AssertionRewriter` runs cvc5's rewriter after NNF and after pattern inference. Quantifiers are rebuilt from rewritten bodies with the pattern list carried across, because cvc5's quantifiers rewriter does miniscoping, prenexing and variable elimination, which in Z3 are separate passes with their own parameters. |
| `m_ng_lift_ite` | `LI_CONSERVATIVE` via `setup_AUFLIA` | **missing.** Lifts `(f s (ite c t1 t2))` to `(ite c (f s t1) (f s t2))` for non-ground terms, so it fires inside quantifier bodies and changes which terms exist for triggers to match. |
| `m_pi_pull_quantifiers` | on | **missing.** When pattern inference finds no trigger, Z3 pulls nested quantifiers and retries. The port gives up, and the quantifier reaches the core triggerless. cvc5's `QuantifiersRewriter::mergePrenex` is the nearest existing machinery. |
| `m_distribute_forall` | on | **missing.** `forall X (and F1..Fn)` becomes a conjunction of foralls, only for quantifiers with no patterns and no no-patterns. It runs *before* pattern inference, so each conjunct gets its own trigger. |
| `flatten_clauses` | on | **half done.** `SmtContext::pushAssertion` does the top-level if-then-else and the distribute-over-a-conjunction case when the other side is a literal. Z3 also distributes when the conjunction's reference count is 1, for which there is no equally cheap test here. |
| `m_refine_inj_axiom` | on | **missing.** |
| `m_pi_use_database` | on via `setup_AUFLIA` | **missing** (pattern database). |
| `set_eliminate_and(true)` | on | **implemented, deliberately off.** `--z3-eliminate-and`. The one knowingly unfaithful default: on the formula studied most closely it does exactly what it should (decisions 3469 → 2856 against Z3's 2590, Boolean variables 7406 → 7076, instances 2171 → 2049) and over the sample it costs nine solved benchmarks. Something downstream is tuned to the conjunctions being there. |

The outer layer — `propagate_values`, `solve_eqs`, `elim_unconstrained`,
`ctx_simplify`, `bound_simplifier` — is cvc5's Preprocessor rather than Z3's,
by instruction. Both solvers do work in that space; the port is not doing
Z3's.

## Not faithful, verified inert here

- **Arrays.** `setup_AUFLIA` calls `setup_arrays()`; the port has no array
  theory. Checked: no `(Array` and no array logic in the 300-file sample
  (logics are UFDTLIA 188, UFDTNIA 46, ALL 39, UFBVDTNIA 23, UFBVDTLIA 4), and
  none of the `ALL` files use arrays either.
- **recfuns, seq/str, FP, datalog, special relations, finite sets,
  polymorphism.** Wired by `setup_unknown`; not ported. No `define-fun-rec` in
  the sample.
- **`theory_datatype`** is ported minus Z3's subterm predicate, the occurs
  check through arrays/sequences/finite sets, and model construction via
  `datatype_factory`. The first two are unreachable without those sorts; a
  datatype nesting one of them marks the search model-unsound rather than
  risking a wrong "sat".

## Deliberately not ported

Proof production, the user propagator, parallel and lookahead search,
consequence finding, lambdas, Z3's label literals, model construction, and
MBQI. MBQI is the one that costs answers: it is why quantified `sat` is always
reported as `unknown`, and why the 14 remaining `unknown` results on the
sample stand — E-matching saturates and there is nothing to pick the next
binding with.

## Order of remaining mechanical work

1. `m_ng_lift_ite = LI_CONSERVATIVE` — active on every benchmark here.
2. `m_pi_pull_quantifiers` — triggerless quantifiers are dead weight in the
   core.
3. `m_distribute_forall` — better triggers for the inferred-pattern
   quantifiers.
4. The remaining half of `flatten_clauses`.
5. `m_refine_inj_axiom`, `m_pi_use_database`.
6. Find out why `set_eliminate_and` loses, since it should not.

Then the bridge, which is the largest remaining item and the only one that is
a design question rather than a transcription.

## How to check a divergence

`README.md` documents the diagnostics. The short version: dump the port's own
preprocessed formula with `--z3-dump-assertions=FILE` and run Z3 on that, so
preprocessing is out of the comparison; then diff `--z3-dump-instances` against
Z3's `-tr:qi_queue` (with `pp.min_alias_size=1000000 pp.max_width=100000000` so
it stops abbreviating with `let`); `--z3-qi-profile` gives Z3's per-quantifier
table keyed by pattern instead of by a generated `qid`. On the UFDTLIA query
used above, Z3 closes the port's own formula with 576 instantiations where the
port makes 2121 and still saturates, which locates the problem in the search
rather than in the matching.
