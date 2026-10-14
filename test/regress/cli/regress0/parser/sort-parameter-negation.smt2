; EXPECT: unsat
(set-logic UFDT)
(declare-sort-parameter A)
(declare-datatype One ((one)))
; Negation stays inside the implicit quantification over sorts.
(assert (not (forall ((x A) (y A)) (= x y))))
(check-sat)
