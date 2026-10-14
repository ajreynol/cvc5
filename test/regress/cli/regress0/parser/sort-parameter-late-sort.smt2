; COMMAND-LINE: --incremental
; DISABLE-TESTER: dump
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
(set-logic UFDT)
(declare-sort-parameter A)
(assert (forall ((x A) (y A) (z A)) (or (= x y) (= x z) (= y z))))
(check-sat)
(push 1)
; This unused declaration still extends the domain of sort instantiation.
(declare-datatype Three ((red) (green) (blue)))
(check-sat)
(pop 1)
(check-sat)
