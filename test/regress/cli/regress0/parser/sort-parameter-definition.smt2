; EXPECT: unsat
(set-logic UFLIA)
(declare-sort-parameter A)
(define-fun id ((x A)) A x)
(assert (not (= (id 0) 0)))
(check-sat)
