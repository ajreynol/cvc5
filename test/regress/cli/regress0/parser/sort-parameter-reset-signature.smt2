; COMMAND-LINE: --incremental
; DISABLE-TESTER: dump
; EXPECT: unsat
; EXPECT: sat
(set-logic UFDT)
(declare-datatype Three ((red) (green) (blue)))
(declare-sort-parameter A)
(assert (forall ((x A) (y A) (z A)) (or (= x y) (= x z) (= y z))))
(check-sat)
(reset-assertions)
(declare-sort-parameter A)
(assert (forall ((x A) (y A) (z A)) (or (= x y) (= x z) (= y z))))
(check-sat)
