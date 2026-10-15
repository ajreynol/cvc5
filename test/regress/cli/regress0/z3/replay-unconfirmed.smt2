; REQUIRES: unrestricted-mode
; COMMAND-LINE: --z3-replay --z3-preset=verus-best --produce-proofs
; COMMAND-LINE: --z3-replay --z3-theory-engine=cvc5 --produce-proofs
; EXPECT: unknown
; A satisfiable answer from the port is not an unsat confirmation.
(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(assert (distinct a b))
(check-sat)
