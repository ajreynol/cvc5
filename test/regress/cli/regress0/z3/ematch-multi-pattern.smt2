; COMMAND-LINE: --z3
; COMMAND-LINE: --z3 --z3-preset=verus-best
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; multi-pattern
(set-logic UF)
(declare-sort U 0) (declare-fun f (U) U) (declare-fun g (U) U)
(declare-fun a () U) (declare-fun p (U U) Bool)
(assert (forall ((x U) (y U)) (! (p (f x) (g y)) :pattern ((f x) (g y)))))
(assert (not (p (f a) (g a))))
(check-sat)
