; COMMAND-LINE: --z3
; EXPECT: unsat
; DISABLE-TESTER: model
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (<= a b))
(assert (<= b a))
(assert (not (= (f a) (f b))))
(check-sat)
