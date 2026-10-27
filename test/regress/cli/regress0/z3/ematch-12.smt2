; COMMAND-LINE: --z3
; EXPECT: unsat
; ground arg that is itself an application
; DISABLE-TESTER: unsat-core
; The unsat core drops the assertions that provide the trigger terms, so
; E-matching answers unknown on the core alone.
(set-logic UFLIA)
(declare-sort U 0) (declare-sort T 0)
(declare-fun ht (U T) Bool) (declare-fun uint (Int) T)
(declare-fun a () U) (declare-fun p (U) Bool)
(assert (forall ((x U)) (! (p x) :pattern ((ht x (uint 8))))))
(assert (ht a (uint 8)))
(assert (not (p a)))
(check-sat)
