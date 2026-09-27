; COMMAND-LINE: --incremental --no-cbqi --user-pat=strict
; COMMAND-LINE: --incremental --no-cbqi --user-pat=strict --term-db-reuse-eqc
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: sat
; REQUIRES: unrestricted-mode
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun g (U) U)
(declare-fun p (U) Bool)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(push 1)
(assert (forall ((x U)) (! (p (f (g x))) :pattern ((f (g x))))))
(push 1)
(assert (= b (g a)))
(assert (not (p (f b))))
(check-sat)
(pop 1)
(push 1)
(assert (= c (g a)))
(assert (not (p (f c))))
(check-sat)
(pop 1)
(assert (not (p (f (g b)))))
(check-sat)
(pop 1)
(assert (not (p (f (g b)))))
(check-sat)
