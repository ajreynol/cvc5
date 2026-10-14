; EXPECT: unsat
(set-logic AUFLIA)
(declare-sort-parameter A)
(declare-sort-parameter B)
(declare-fun p ((Array A B)) Bool)
(assert (forall ((a (Array A B))) (p a)))
(declare-const ints (Array Int Int))
(assert (not (p ints)))
(check-sat)
