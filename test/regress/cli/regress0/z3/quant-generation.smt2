; COMMAND-LINE: --z3
; COMMAND-LINE: --z3 --z3-prop-engine=z3 --z3-preset=z3
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun a () U)
(declare-fun p (U) Bool)
(assert (forall ((x U)) (! (=> (p x) (p (f x))) :pattern ((p x)))))
(assert (p a))
(assert (not (p (f (f (f (f a)))))))
(check-sat)
