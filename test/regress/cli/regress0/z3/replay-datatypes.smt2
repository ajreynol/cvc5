; REQUIRES: unrestricted-mode
; COMMAND-LINE: --z3-replay --z3-preset=verus-best --produce-proofs
; COMMAND-LINE: --z3-replay --z3-preset=verus-best --z3-prop-engine=cvc5 --produce-proofs
; COMMAND-LINE: --z3-replay --z3-preset=verus-best --z3-theory-engine=cvc5 --produce-proofs
; EXPECT: unsat
; The port must undo datatype trails before destroying their variable data.
; Native solving continues after the port is destroyed.
(set-logic QF_UFDTLIA)
(declare-datatype Lst ((nil) (cons (hd Int) (tl Lst))))
(declare-const x Lst)
(declare-const y Lst)
(assert (= x (cons 1 y)))
(assert (= y (cons 2 x)))
(check-sat)
