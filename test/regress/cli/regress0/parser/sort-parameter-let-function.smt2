; EXPECT: unsat
(set-logic UF)
(declare-sort-parameter A)
(declare-fun f (A) A)
(assert (forall ((x A)) (let ((g f)) (not (= (g x) (f x))))))
(check-sat)
