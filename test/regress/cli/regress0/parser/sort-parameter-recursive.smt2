; EXPECT: unsat
(set-logic UFLIA)
(declare-sort-parameter A)
(define-fun-rec choose ((n Int) (x A)) A
  (ite (<= n 0) x (choose (- n 1) x)))
(assert (not (= (choose 2 7) 7)))
(check-sat)
