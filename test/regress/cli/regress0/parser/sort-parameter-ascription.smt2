; EXPECT: unsat
(set-logic UFLIA)
(declare-sort-parameter A)
(declare-sort-parameter B)
(declare-fun f (A) B)
(declare-const c A)
(assert (forall ((x A)) (= ((as f B) x) (as c B))))
(assert (not (= ((as f Int) false) (as c Int))))
(check-sat)
