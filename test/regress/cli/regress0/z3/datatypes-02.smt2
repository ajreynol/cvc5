; COMMAND-LINE: --z3
; COMMAND-LINE: --z3 --z3-prop-engine=z3 --z3-preset=z3
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
(set-logic QF_UFDTLIA)
(declare-datatype Lst ((nil) (cons (hd Int) (tl Lst))))
(declare-fun x () Lst)
(declare-fun y () Lst)
(assert (= x (cons 1 y)))
(assert (= y (cons 2 x)))
(check-sat)
