; COMMAND-LINE: --z3
; COMMAND-LINE: --z3 --z3-prop-engine=z3 --z3-preset=z3
; COMMAND-LINE: --z3 --z3-prop-engine=z3
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; same, but the ground arg matches only modulo equality
(set-logic UF)
(declare-sort U 0) (declare-sort T 0)
(declare-fun ht (U T) Bool) (declare-fun nat () T) (declare-fun t2 () T)
(declare-fun a () U) (declare-fun p (U) Bool)
(assert (forall ((x U)) (! (p x) :pattern ((ht x nat)))))
(assert (= t2 nat))
(assert (ht a t2))
(assert (not (p a)))
(check-sat)
