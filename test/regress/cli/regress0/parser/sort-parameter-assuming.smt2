; EXPECT: sat
(set-logic UF)
(declare-sort-parameter A)
(check-sat-assuming ((not (forall ((x A) (y A)) (= x y)))))
