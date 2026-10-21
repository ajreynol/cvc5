; COMMAND-LINE: --z3
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: unsat-core
(set-logic UF)
(declare-sort U 0) (declare-fun f (U U) U) (declare-fun h (U) U)
(declare-fun a () U) (declare-fun b () U) (declare-fun c () U)
(declare-fun p (U) Bool) (declare-fun r (U) Bool)
(assert (forall ((x U) (y U)) (! (p (f x y)) :pattern ((f (h x) y)))))
(assert (= a (h b)))
(assert (r (f a c)))
(assert (not (p (f b c))))
(check-sat)
