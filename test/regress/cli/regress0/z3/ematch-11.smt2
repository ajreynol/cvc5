; COMMAND-LINE: --z3
; EXPECT: unsat
; ground arg plus a nested function in the pattern
; DISABLE-TESTER: unsat-core
; The unsat core drops the assertions that provide the trigger terms, so
; E-matching answers unknown on the core alone.
(set-logic UF)
(declare-sort U 0) (declare-sort T 0)
(declare-fun ht (U T) Bool) (declare-fun nat () T)
(declare-fun bx (U) U) (declare-fun a () U) (declare-fun p (U) Bool)
(assert (forall ((x U)) (! (p x) :pattern ((ht (bx x) nat)))))
(assert (ht (bx a) nat))
(assert (not (p a)))
(check-sat)
