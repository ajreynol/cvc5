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
| `src/z3/util/` | Data structures and the term interface: literals, regions, trails, hashing, `types.h`, `ast.h` (incl. `QuantifierNormalizer`), and `statistics` | nothing outside `z3/util/` |
| `src/z3/relevancy/` | The Boolean side: `PropCore` (assignment, clauses, watch lists, propagation), `RelevancyPropagator`, `RelevancyTracker` (the `TheoryEngineModule` that hands it every asserted literal), and `TheorySide`, the interface through which it reaches the theory side | `z3/util/` only |
| `src/z3/quantifiers/` | The theory side and the cvc5 integration: `SmtContext` (E-graph, internalizer), `mam` (E-matching), `QiQueue`, the checker, the quantifier manager, `HostCore` (which owns the core), `LemmaProofGenerator`, `ShadowFeed`, `Z3Module` | anything |

The rules are kept by an interface, `TheorySide`
(`relevancy/theory_side.h`): what `PropCore` and `RelevancyPropagator` need
from the theory side. `SmtContext` implements it.

The core takes the input as cvc5's preprocessing leaves it, from
`ppNotifyAssertions`. It renames the quantified variables to the canonical
ones it expects (`QuantifierNormalizer`) at its boundary: `HostCore` renames
the formulas, atoms and literals that come from cvc5 (`toCore`), and gives
cvc5 its own atoms back in the lemmas and queries it sends (`toHost`). cvc5
preprocesses the core's lemmas as any other, and the core takes them in that
form.

All of the port's classes are in the namespace `cvc5::internal::z3`.

## Hooks in cvc5

Outside the directories above, the port touches:

- `QuantifiersModules` makes `Z3Module`, and no other module, under `--z3`.
  `QuantifiersModule::finishInit` and `notifyMasterMerge` give it the theory
  engine and the merges of the master equality engine.
- `TheoryEngineModule::notifyFact` / `needsFacts` and
  `TheoryEngine::addModule` are used by `RelevancyTracker`.
- `Skolemize::getSkolemizationLemma` gives the core the lemma with which the
  quantifiers engine skolemized a formula, with its proof.
- `DecisionManager::STRAT_QUANT_Z3_SPLIT`: the core asks cvc5 to decide the
  atoms its relevancy needs assigned through a decision strategy.
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
  `--term-db-mode=all`: the core does not use cvc5's term database, which in
  the default mode walks every asserted fact at each check.

## Size

C++ lines (code lines exclude blank and comment lines, as cloc counts them),
as of this README:

| Directory | Files | Code | Comment | Blank |
|---|---:|---:|---:|---:|
| `src/z3/util/` | 14 | 1415 | 481 | 326 |
| `src/z3/relevancy/` | 12 | 2275 | 521 | 374 |
| `src/z3/quantifiers/` | 27 | 8186 | 1586 | 1038 |
| **Total** | 53 | **11876** | 2588 | 1738 |

The rest of cvc5 changes by 236 added and 15 deleted lines over 18 C++ files,
most of them in `smt/set_defaults.cpp` (the capability checks) and
`theory/quantifiers/quantifiers_preprocess.cpp` (pre-skolemization of
quantified formulas with patterns).
