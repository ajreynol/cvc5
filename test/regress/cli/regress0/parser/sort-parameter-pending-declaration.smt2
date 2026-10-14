; COMMAND-LINE: --incremental
; DISABLE-TESTER: dump
; EXPECT: sat
; EXPECT: unsat
(set-logic UFDT)
(declare-sort-parameter A)
(assert (forall ((x A) (y A) (z A)) (or (= x y) (= x z) (= y z))))
(check-sat-assuming (true))
(declare-datatype Three ((red) (green) (blue)))
(check-sat)
