; EXPECT: unsat
(set-logic UF)
(declare-sort-parameter A)
(assert (forall ((x A) (y A)) (= x y)))
(check-sat)
