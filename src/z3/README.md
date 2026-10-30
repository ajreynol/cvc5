# The ported Z3 core (`--z3`)

A port of Z3's E-matching core, which runs as the only module of cvc5's
quantifiers engine (`Z3Module`). cvc5's own prop engine and theories do the
ground reasoning, and cvc5's quantifiers engine registers the quantified
formulas and skolemizes those asserted false (the core takes that lemma when
the formula is relevant to it); the core keeps a shadow of the ground state (an
E-graph, and a Boolean mirror of the SAT assignment for Z3's relevancy), sends
quantifier instances and delayed units to cvc5 as lemmas, and asks it for
decisions. Since it sends only lemmas, it never explains anything, and keeps no
justifications.

Its lemmas have proofs (`LemmaProofGenerator`), made when they are asked for:
an instance is sent as cvc5's instantiation lemma, proven by `INSTANTIATE`, a
skolemization with the proof of cvc5's `Skolemize`, and a delayed unit by
weakening; cvc5's preprocessing proves the form the core takes them in.

## Layout and inclusion rules

| Directory | Contents | May include (from the port) |
|---|---|---|
| `src/z3/relevancy/` | The Boolean side, over cvc5's `prop::SatLiteral`: `PropCore` (variables, assignment, clauses, watch lists, Boolean propagation), `RelevancyPropagator`, and `RelevancyTracker` (the `TheoryEngineModule` that hands it every asserted literal) | `z3/quantifiers/` (`SmtContext`, the trail stack, the statistics) |
| `src/z3/quantifiers/` | The coordinator and the cvc5 integration: `Z3Module` (the boundary with cvc5), `SmtContext` (internalizer, propagation and scopes), `EGraph`, `mam` (E-matching), `QiQueue`, the checker, the quantifier manager, `LemmaProofGenerator`, and the shared pieces: the trail stack (on a `context::Context` of its own), the statistics, and `QuantifierNormalizer` | anything |

`PropCore` and `RelevancyPropagator` reach the theory side, `SmtContext`,
directly, so the two directories depend on each other.

The core takes the input as cvc5's preprocessing leaves it, from
`ppNotifyAssertions`. It renames the quantified variables to the canonical
ones it expects (`QuantifierNormalizer`) at its boundary: `Z3Module` renames
the formulas, atoms and literals that come from cvc5 (`toCore`), and gives
cvc5 its own atoms back in the lemmas and queries it sends (`toHost`). cvc5
preprocesses the core's lemmas as any other, and the core takes them in that
form.

All of the port's classes are in the namespace `cvc5::internal::z3`.

## Ownership

Each class owns the ones below it; `(-> X)` is a reference it keeps to X.
`Z3Module` drives `SmtContext`, which calls it back only to send its
instances, skolemizations and lemmas (`mkInstance`, `mkSkolemization`,
`sendLemma`). `SmtContext` drives the others; their references to it are for
notifications (`PropCore`: an atom assigned, a term relevant, a variable
deleted; `EGraph`: a merge, of Boolean classes, a conflict) and for what it
coordinates (the trail stack, relevancy, the statistics).

```
QuantifiersEngine (cvc5)
└── Z3Module                      the module of cvc5's quantifiers engine, and
    │                             the boundary with cvc5: facts, checks,
    │                             lemmas and their proofs, following
    │                             the SAT context
    ├── LemmaProofGenerator
    ├── PopNotify                 a ContextNotifyObj on the SAT context
    │                                                   (-> Z3Module)
    ├── RelevancyTracker          registered with TheoryEngine::addModule:
    │                             the literals the SAT solver asserts
    │                                                   (-> Z3Module)
    └── SmtContext                the core: input, internalization,
        │                         propagation and scopes   (-> Z3Module)
        ├── Statistics
        ├── TrailStack            its own context::Context, and the memory of
        │                         the enodes, relevancy handlers, fingerprints
        │                         and code trees
        ├── PropCore              the Boolean side     (-> SmtContext)
        │   └── RelevancyPropagator                     (-> PropCore, SmtContext)
        ├── EGraph                the enodes, congruence closure, generations,
        │   │                     and the merges of the master equality engine
        │   │                                           (-> SmtContext)
        │   └── CgTable, TmpENode
        ├── QuantifierNormalizer
        └── QuantifierManager                           (-> SmtContext)
            ├── QiQueue                                 (-> QuantifierManager,
            │   │                                           SmtContext)
            │   └── Checker                             (-> SmtContext, EGraph)
            ├── FingerprintSet                          (-> TrailStack)
            └── Mam x2, eager and lazy (MamImpl: LabelHasher,
                CodeTreeManager, Compiler, Interpreter, CodeTreeMap)
                                                        (-> SmtContext, EGraph,
                                                            QuantifierManager,
                                                            TrailStack)
```

## Hooks in cvc5

Outside the directories above, the port touches:

- `QuantifiersModules` makes `Z3Module` under `--z3`, first, then cvc5's own
  modules as their options select them. `--z3` sets
  `--inst-when=last-call-delay`, so that these instantiate only on a complete
  model, once the core and every theory are done, and turns off
  conflict-based instantiation (`--cbqi`).
  `QuantifiersModule::finishInit` and `notifyMasterMerge` give it the theory
  engine and the merges of the master equality engine.
- `TermDb` and `InstEvaluatorManager` do not reset at standard effort, where
  only the core checks, at every check.
- `TheoryEngineModule::notifyFact` / `needsFacts` and
  `TheoryEngine::addModule` are used by `RelevancyTracker`.
- `Skolemize::getSkolemizationLemma` gives the core the lemma with which the
  quantifiers engine skolemized a formula, with its proof.
- `PropEngine` uses `FormulaLitPolicy::TRACK_AND_NOTIFY_VAR` under `--z3`, so
  Boolean variables reach the core.
- `SetDefaults::checkZ3Capabilities` refuses what the core does not support:
  `--incremental`, `--deep-restart`, sygus (and so interpolants and abducts),
  oracles, and `--dump-instantiations` without proofs (the instantiations are
  read from the proof). Unsat cores default to `--unsat-cores-mode=sat-proof`,
  since deciding on the input as assumptions first hurts the core's search.
  `setDefaultsQuantifiers` sets `--pre-skolem-quant=agg`: the existentials
  nested in quantified formulas get skolem functions of the enclosing
  variables, as in Z3's negation normal form, which `QuantifiersPreprocess`
  now also applies to quantified formulas with patterns. It also sets
  `--inst-when=last-call-delay` and turns off `--cbqi`, as above, and sets
  `--arith-implied-eqs`, see below.

## Arithmetic equalities (`--arith-implied-eqs`)

The worst files of the Verus set (in `quant-07-25/slow`: cs56, cs65, cs100,
cs102 ...) ran out of resources under `--z3` while Z3 solves them in about
0.1s: a matching loop over the sequence axioms (`axiom_seq_add_index*`) and
`prelude_add`/`prelude_sub` nests terms
`Add(%I(I(Sub(%I(I(Add ... i ... len ... len)))))` without end. Z3 breaks it
with the equalities its arithmetic propagates to the E-graph
(`smt.arith.propagate_eqs`, on by default; `theory_arith_eq.h`): each new term
is found equal to `i` and joins an existing class, so it makes no new match.
With `smt.arith.propagate_eqs=false`, Z3 loops in the same way.

cvc5's linear arithmetic now finds the same equalities, under
`--arith-implied-eqs`, which `--z3` sets. It is not specific to the core:
`ImpliedEqualities` (`theory/arith/linear/implied_equalities.{h,cpp}`) visits,
at the end of each standard check, the rows of the tableau of the variables
fixed (equal bounds) since the last check. A row whose variables are fixed
but

- x, fixes x to a value c: x = c;
- x and y, of opposite coefficients, gives an offset x = y + k; with k = 0,
  x = y, and two variables at the same offset from y are equal (a table of
  offsets, in the SAT context).

`ArithCongruenceManager::impliedEquality` asserts the equalities between terms
of arithmetic's equality engine to it, explained by the bounds of the fixed
variables, with a proof (two sums of these bounds,
`MACRO_ARITH_SCALE_SUM_UB`, and `ARITH_TRICHOTOMY`). From there they reach the
other theories (without a split of theory combination), the master equality
engine and so cvc5's E-matching, and the core, through the merges of the master
equality engine it already takes.

Results on the 388 Verus files (`--rlimit=10000000`):

- `--z3`: 373 to 379 solved (cs56, cs63, cs65, cs78, cs100, cs102), none
  lost, 0.91 of the time on the common files (geometric mean). The equalities
  to a value (x = c) account for 3 of the 6.
- cvc5 without `--z3`, with `--arith-implied-eqs`: 370 to 371 (cs63), none
  lost, 0.92 of the time. It is off by default there.

Known issues and to do:

- Strings: with the option forced on, 6 strings regressions time out (e.g.
  `regress0/proofs/proj-issue777-open-eqproof.smt2`). The equalities to a value
  give exact lengths to the strings solver, explained by the bound of whatever
  length it is currently trying, so the conflicts it learns are specific to
  that length and its length enumeration does not terminate.
- cs150 and cs151 still loop: there `len` is not fixed, and the offset only
  appears after substituting one row in another (`A = S + len`,
  `S = i - len`). The rows are visited only when one of their variables is
  fixed, not after pivoting; check which rows Z3 examines
  (`propagate_cheap_eq`, `fixed_var_eh`) and do the same.

Also measured: only about half of the arithmetic literals and 12% to 33% of
the datatype literals that cvc5 asserts to its theories are relevant to the
core. Z3 asserts only relevant literals to its theories, so filtering cvc5's
theory facts by the core's relevancy is the next larger lever.

## Size

C++ lines (code lines exclude blank and comment lines, as cloc counts them),
as of this README:

| Directory | Files | Code | Comment | Blank |
|---|---:|---:|---:|---:|
| `src/z3/relevancy/` | 10 | 1512 | 399 | 264 |
| `src/z3/quantifiers/` | 26 | 7532 | 1760 | 960 |
| **Total** | 36 | **9044** | 2159 | 1224 |

The rest of cvc5 changes by 730 added and 18 deleted lines over 28 C++ files,
most of them in `theory/arith/linear` (the implied equalities, 468 lines),
`smt/set_defaults.cpp` (the capability checks) and
`theory/quantifiers/quantifiers_preprocess.cpp` (pre-skolemization of
quantified formulas with patterns).
