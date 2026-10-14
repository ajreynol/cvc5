; EXPECT: unsat
(set-logic UFDT)
(declare-sort-parameter A)
(declare-datatype One ((one)))
; The defined constant has no sort parameters, but its body does.
(define-fun singleton () Bool (forall ((x A) (y A)) (= x y)))
(check-sat)
