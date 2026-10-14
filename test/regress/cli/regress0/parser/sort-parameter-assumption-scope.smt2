; COMMAND-LINE: --incremental
; DISABLE-TESTER: dump
; EXPECT: unsat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
(set-logic UF)
(declare-sort-parameter A)
(check-sat-assuming ((forall ((x A) (y A)) (= x y))))
(check-sat)
(push 1)
(assert (forall ((x A) (y A)) (= x y)))
(check-sat)
(pop 1)
(check-sat)
