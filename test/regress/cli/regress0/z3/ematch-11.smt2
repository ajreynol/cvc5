; COMMAND-LINE: --z3
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: unsat-core
; ground arg plus a nested function in the pattern
(set-logic UF)
(declare-sort U 0) (declare-sort T 0)
(declare-fun ht (U T) Bool) (declare-fun nat () T)
(declare-fun bx (U) U) (declare-fun a () U) (declare-fun p (U) Bool)
(assert (forall ((x U)) (! (p x) :pattern ((ht (bx x) nat)))))
(assert (ht (bx a) nat))
(assert (not (p a)))
(check-sat)
