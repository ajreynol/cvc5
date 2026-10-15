; REQUIRES: unrestricted-mode
; COMMAND-LINE: --z3-replay --z3-preset=verus-best --produce-proofs
; COMMAND-LINE: --z3-replay --z3-theory-engine=cvc5 --produce-proofs
; EXPECT: unsat
; There need not be any quantified formulas or recorded instances.
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
