; COMMAND-LINE: --z3
; EXPECT: unsat
; three nested levels
(set-logic UF)
(declare-sort U 0) (declare-fun f (U) U) (declare-fun g (U) U) (declare-fun h (U) U)
(declare-fun a () U) (declare-fun p (U) Bool)
(assert (forall ((x U)) (! (p (h (g (f x)))) :pattern ((h (g (f x)))))))
(assert (not (p (h (g (f a))))))
(check-sat)
