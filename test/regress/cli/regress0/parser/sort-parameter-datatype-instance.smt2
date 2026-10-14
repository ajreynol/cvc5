; EXPECT: unsat
(set-logic UFDTLIA)
(declare-sort-parameter A)
(declare-datatype Box (par (T) ((box (value T)))))
(declare-fun p ((Box A)) Bool)
(assert (forall ((x (Box A))) (p x)))
(assert (not (p (box 0))))
(check-sat)
