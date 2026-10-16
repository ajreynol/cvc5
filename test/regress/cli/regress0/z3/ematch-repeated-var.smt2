; COMMAND-LINE: --z3
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; repeated variable pattern f(x,x)
(set-logic UF)
(declare-sort U 0) (declare-fun f (U U) U) (declare-fun a () U) (declare-fun p (U) Bool)
(assert (forall ((x U)) (! (p (f x x)) :pattern ((f x x)))))
(assert (not (p (f a a))))
(check-sat)
