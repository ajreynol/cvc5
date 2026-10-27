; COMMAND-LINE: --z3
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
; The unsat core drops the assertions that provide the trigger terms, so
; E-matching answers unknown on the core alone.
(set-logic UF)
(declare-sort U 0) (declare-fun f (U) U) (declare-fun g (U) U)
(declare-fun a () U) (declare-fun b () U)
(declare-fun p (U) Bool) (declare-fun r (U) Bool)
(assert (forall ((x U)) (! (p x) :pattern ((f (g x))))))
(assert (= b (g a)))
(assert (r (f b)))
(assert (not (p a)))
(check-sat)
