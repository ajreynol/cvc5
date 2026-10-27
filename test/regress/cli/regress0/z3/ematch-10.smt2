; COMMAND-LINE: --z3
; EXPECT: unsat
; same, but the ground arg matches only modulo equality
; DISABLE-TESTER: unsat-core
; The unsat core drops the assertions that provide the trigger terms, so
; E-matching answers unknown on the core alone.
(set-logic UF)
(declare-sort U 0) (declare-sort T 0)
(declare-fun ht (U T) Bool) (declare-fun nat () T) (declare-fun t2 () T)
(declare-fun a () U) (declare-fun p (U) Bool)
(assert (forall ((x U)) (! (p x) :pattern ((ht x nat)))))
(assert (= t2 nat))
(assert (ht a t2))
(assert (not (p a)))
(check-sat)
