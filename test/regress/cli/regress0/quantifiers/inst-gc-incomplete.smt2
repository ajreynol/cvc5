; With --inst-gc=assert the SAT solver may discard the clause asserting an
; instantiation, and the instantiation cache will not produce it again, so
; "sat" may not be concluded. Answers unknown where the default answers sat.
; COMMAND-LINE: --finite-model-find --inst-gc=assert
; EXPECT: unknown
(set-logic UF)
(declare-sort U 0)
(declare-fun p (U) Bool)
(declare-fun q (U) Bool)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(assert (distinct a b c))
(assert (forall ((x U)) (or (p x) (q x))))
(assert (not (p a)))
(assert (not (q b)))
(check-sat)
