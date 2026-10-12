; COMMAND-LINE: --z3
; COMMAND-LINE: --z3 --z3-preset=verus-best
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; pattern with a ground second argument
(set-logic UF)
(declare-sort U 0) (declare-sort T 0)
(declare-fun ht (U T) Bool) (declare-fun nat () T) (declare-fun int () T)
(declare-fun a () U) (declare-fun p (U) Bool)
(assert (forall ((x U)) (! (p x) :pattern ((ht x nat)))))
(assert (ht a nat))
(assert (not (p a)))
(check-sat)
