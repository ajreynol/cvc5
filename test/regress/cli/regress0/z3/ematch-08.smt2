; COMMAND-LINE: --z3
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
; The unsat core drops the assertions that provide the trigger terms, so
; E-matching answers unknown on the core alone.
(set-logic UF)
(declare-sort U 0) (declare-fun f (U) U) (declare-fun g (U) U)
(declare-fun a () U) (declare-fun p (U) Bool) (declare-fun q (U) Bool)
(declare-fun r (U) Bool)
(assert (forall ((x U)) (! (q (g x)) :pattern ((f x)))))
(assert (forall ((x U)) (! (p x) :pattern ((q x)))))
(assert (r (f a)))
(assert (not (p (g a))))
(check-sat)
