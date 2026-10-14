; EXPECT: unknown
(set-logic ALL)
(declare-sort-parameter A)
(declare-sort-parameter B)
(declare-const a (Array A B))
(declare-fun p ((Array A B)) Bool)
(assert (p a))
(check-sat)
