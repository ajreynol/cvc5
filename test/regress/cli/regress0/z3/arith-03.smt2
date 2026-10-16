; COMMAND-LINE: --z3
; COMMAND-LINE: --z3 --z3-slots=quantifiers
; COMMAND-LINE: --z3 --z3-prop-engine=z3 --z3-preset=z3
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(assert (forall ((y Int)) (! (= (f y) 0) :pattern ((f y)))))
(assert (= x 3))
(assert (not (= (f (+ x 0)) 0)))
(check-sat)
