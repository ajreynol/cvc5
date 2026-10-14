; COMMAND-LINE: --term-db-mode=relevance --no-cbqi
; EXPECT: unsat
; The trigger term (g c) occurs only in the body of the instance for x -> c.
; Since instances are roots for relevance, (g c) is admitted for matching.
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun g (U) U)
(declare-fun P (U) Bool)
(declare-fun Q (U) Bool)
(declare-const c U)
(declare-const B Bool)
(assert (or B (P (f c))))
(assert (not B))
(assert (forall ((x U)) (! (or (P (g x)) (Q (g x))) :pattern ((f x)))))
(assert (forall ((y U)) (! (not (P (g y))) :pattern ((g y)))))
(assert (forall ((y U)) (! (not (Q (g y))) :pattern ((g y)))))
(check-sat)
