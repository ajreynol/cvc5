; COMMAND-LINE: --incremental --global-declarations
; DISABLE-TESTER: dump
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
(set-logic UFDT)
(declare-sort-parameter A)
(assert (forall ((x A) (y A) (z A)) (or (= x y) (= x z) (= y z))))
(check-sat-assuming (true))
(push 1)
(declare-datatype Three ((red) (green) (blue)))
(pop 1)
(check-sat)
(reset-assertions)
(assert (forall ((x A) (y A) (z A)) (or (= x y) (= x z) (= y z))))
(check-sat)
