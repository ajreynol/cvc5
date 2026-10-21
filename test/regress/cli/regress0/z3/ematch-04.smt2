; COMMAND-LINE: --z3
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: unsat-core
; pattern with ground subterm f(x,a)
(set-logic UF)
(declare-sort U 0) (declare-fun f (U U) U) (declare-fun a () U) (declare-fun b () U)
(declare-fun p (U) Bool)
(assert (forall ((x U)) (! (p (f x a)) :pattern ((f x a)))))
(assert (not (p (f b a))))
(check-sat)
