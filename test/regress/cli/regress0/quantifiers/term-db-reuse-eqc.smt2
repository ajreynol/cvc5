; COMMAND-LINE: --no-cbqi --user-pat=strict
; COMMAND-LINE: --no-cbqi --user-pat=strict --term-db-reuse-eqc
; EXPECT: unsat
; REQUIRES: unrestricted-mode
(set-logic UF)
(declare-sort U 0)
(declare-fun h (U) U)
(declare-fun s (U) U)
(declare-fun k (U) U)
(declare-fun p (U) Bool)
(declare-fun q (U) Bool)
(declare-fun r (U) Bool)
(declare-const a U)
(declare-const b U)
; The p/h chain needs several rounds; the k index can stay unchanged.
(assert (forall ((x U)) (! (=> (p (h x)) (p (h (s x))))
                          :pattern ((p (h x))))))
(assert (forall ((x U)) (! (=> (q (k x)) (r x))
                          :pattern ((q (k x))))))
(assert (q (k b)))
(assert (p (h a)))
(assert (not (p (h (s (s (s a)))))))
(check-sat)
