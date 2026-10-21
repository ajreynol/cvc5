# The ported Z3 core (`--z3`)

A port of Z3's E-matching core, which runs as cvc5's quantifiers engine
(`Z3QuantifiersEngine`). cvc5's own prop engine and theories do the ground
reasoning; the core keeps a shadow of the ground state (an E-graph, and a
Boolean mirror of the SAT assignment for Z3's relevancy) and sends quantifier
instances, splits and delayed units to cvc5 as lemmas. Since it sends
only lemmas, it never explains anything, and keeps no justifications.

## Layout and inclusion rules

| Directory | Contents | May include (from the port) |
|---|---|---|
| `src/z3/util/` | Data structures and the term interface: literals, regions, trails, hashing, `types.h`, `ast.h` (incl. `QuantifierNormalizer`), and `params`, `statistics` | nothing outside `z3/util/` |
| `src/z3/relevancy/` | The Boolean side: `PropCore` (assignment, clauses, watch lists, propagation), `RelevancyPropagator`, `RelevancyTracker` (the `TheoryEngineModule` that hands it every asserted literal), and `TheorySide`, the interface through which it reaches the theory side | `z3/util/` only |
| `src/z3/quantifiers/` | The theory side and the cvc5 integration: `SmtContext` (E-graph, internalizer), `mam` (E-matching), `QiQueue`, the checker, the quantifier manager, `HostCore` (which owns the core), `ShadowFeed`, `Z3QuantifiersEngine` | anything |

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

- `TheoryQuantifiers` constructs `Z3QuantifiersEngine` under `--z3`.
- `QuantifiersEngine` has virtual methods, for the subclass, which ignores
  `assertQuantifier`: the core takes the quantified formulas with every other
  literal.
- `TheoryEngineModule::notifyFact` / `needsFacts` and
  `TheoryEngine::addModule` are used by `RelevancyTracker`.
- `Theory::checksWithoutFacts`: the quantifiers theory is checked even without
  new facts.
- `PropEngine` uses `FormulaLitPolicy::TRACK_AND_NOTIFY_VAR` under `--z3`, so
  Boolean variables reach the core. The `UNPROCESSED` lemma property keeps
  cvc5 from preprocessing lemmas the core has already preprocessed.
- `Skolemize::getSkolemizationLemma` lets the core reuse cvc5's native
  skolemization lemma.
- `SetDefaults::checkZ3Capabilities` refuses what the core does not support
  (`--incremental`, models, proofs, unsat cores, and others), and
  `setDefaultsQuantifiers` sets `--pre-skolem-quant=agg`: the existentials
  nested in quantified formulas get skolem functions of the enclosing
  variables, as in Z3's negation normal form, which `QuantifiersPreprocess`
  now also applies to quantified formulas with patterns.

## Size

C++ lines (code lines exclude blank and comment lines, as cloc counts them),
as of this README:

| Directory | Files | Code | Comment | Blank |
|---|---:|---:|---:|---:|
| `src/z3/util/` | 16 | 1458 | 526 | 341 |
| `src/z3/relevancy/` | 12 | 2278 | 521 | 374 |
| `src/z3/quantifiers/` | 27 | 8562 | 1532 | 1059 |
| **Total** | 55 | **12298** | 2579 | 1774 |

The rest of cvc5 changes by 288 added and 35 deleted lines over 15 C++ files,
most of them in `smt/set_defaults.cpp` (the capability checks) and
`theory/quantifiers/theory_quantifiers.cpp`.
