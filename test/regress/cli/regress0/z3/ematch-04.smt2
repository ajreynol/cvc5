; COMMAND-LINE: --z3
; COMMAND-LINE: --z3 --z3-slots=quantifiers
; COMMAND-LINE: --z3 --z3-slots=quantifiers --no-z3-shadow-plugins
; COMMAND-LINE: --z3 --z3-prop-engine=z3 --z3-preset=z3
; COMMAND-LINE: --z3 --z3-prop-engine=z3
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; pattern with ground subterm f(x,a)
(set-logic UF)
(declare-sort U 0) (declare-fun f (U U) U) (declare-fun a () U) (declare-fun b () U)
(declare-fun p (U) Bool)
(assert (forall ((x U)) (! (p (f x a)) :pattern ((f x a)))))
(assert (not (p (f b a))))
(check-sat)
