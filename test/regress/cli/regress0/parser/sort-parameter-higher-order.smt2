; EXPECT: unsat
(set-logic HO_UF)
(declare-sort-parameter A)
(define-fun id ((x A)) A x)
(declare-fun f (Bool) Bool)
(assert (not (= (@ ((as id (-> Bool Bool)) f) true) (f true))))
(check-sat)
