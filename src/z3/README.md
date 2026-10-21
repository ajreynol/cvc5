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
| `src/z3/util/` | Data structures and the term interface: literals, regions, trails, hashing, `types.h`, `ast.h` (incl. `QuantifierNormalizer`), and `params`, `statistics` | nothing outside `z3/util/` |
| `src/z3/relevancy/` | The Boolean side: `PropCore` (assignment, clauses, watch lists, propagation), `RelevancyPropagator`, `RelevancyTracker` (the `TheoryEngineModule` that hands it every asserted literal), and `TheorySide`, the interface through which it reaches the theory side | `z3/util/` only |
| `src/z3/quantifiers/` | The theory side and the cvc5 integration: `SmtContext` (E-graph, internalizer), `mam` (E-matching), `QiQueue`, the checker, the quantifier manager, `HostCore` (which owns the core), `ShadowFeed`, `Z3Module` | anything |

The rules are kept by an interface, `TheorySide`
(`relevancy/theory_side.h`): what `PropCore` and `RelevancyPropagator` need
from the theory side. `SmtContext` implements it.

The core takes the input as cvc5's preprocessing leaves it, from
`ppNotifyAssertions`. It renames the quantified variables to the canonical
ones it expects (`QuantifierNormalizer`) at its boundary: `HostCore` renames
the formulas, atoms and literals that come from cvc5 (`toCore`), and gives
cvc5 its own atoms back in the lemmas and queries it sends (`toHost`).

All of the port's classes are in the namespace `cvc5::internal::z3`.

## Hooks in cvc5

Outside the directories above, the port touches:

- `QuantifiersModules` makes `Z3Module`, and no other module, under `--z3`.
  `QuantifiersModule::finishInit` and `eqNotifyMerge` give it the theory
  engine and the merges of the master equality engine.
- `QuantifiersEngine` still has virtual methods, from the subclass that the
  module replaced.
- `TheoryEngineModule::notifyFact` / `needsFacts` and
  `TheoryEngine::addModule` are used by `RelevancyTracker`.
- `Theory::checksWithoutFacts`: the quantifiers theory is checked even without
  new facts.
- `Skolemize::getSkolemizationLemma` gives the core the lemma with which the
  quantifiers engine skolemized a formula.
- `PropEngine` uses `FormulaLitPolicy::TRACK_AND_NOTIFY_VAR` under `--z3`, so
  Boolean variables reach the core. The `UNPROCESSED` lemma property keeps
  cvc5 from preprocessing lemmas the core has already preprocessed.
- `SetDefaults::checkZ3Capabilities` refuses what the core does not support
  (`--incremental`, models, proofs, unsat cores, and others), and
  `setDefaultsQuantifiers` sets `--pre-skolem-quant=agg`: the existentials
  nested in quantified formulas get skolem functions of the enclosing
  variables, as in Z3's negation normal form, which `QuantifiersPreprocess`
  now also applies to quantified formulas with patterns. It also sets
  `--term-db-mode=all`: the core does not use cvc5's term database, which in
  the default mode walks every asserted fact at each check.

## Size

C++ lines (code lines exclude blank and comment lines, as cloc counts them),
as of this README:

| Directory | Files | Code | Comment | Blank |
|---|---:|---:|---:|---:|
| `src/z3/util/` | 16 | 1457 | 525 | 341 |
| `src/z3/relevancy/` | 12 | 2278 | 521 | 374 |
| `src/z3/quantifiers/` | 27 | 8446 | 1489 | 1042 |
| **Total** | 55 | **12181** | 2535 | 1757 |

The rest of cvc5 changes by 295 added and 32 deleted lines over 17 C++ files,
most of them in `smt/set_defaults.cpp` (the capability checks) and
`theory/quantifiers/quantifiers_preprocess.cpp` (pre-skolemization of
quantified formulas with patterns).
