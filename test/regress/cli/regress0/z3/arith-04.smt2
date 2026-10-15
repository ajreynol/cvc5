; COMMAND-LINE: --z3
; COMMAND-LINE: --z3 --z3-prop-engine=z3 --z3-preset=z3
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (<= a b))
(assert (<= b a))
(assert (not (= (f a) (f b))))
(check-sat)
