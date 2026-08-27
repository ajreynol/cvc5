; note: cpc reference checking not supported, the Relation and Table sort aliases have no Eunoia equivalent, define is not variadic
; DISABLE-TESTER: cpc
; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(assert (= x y))
(assert (not (= (rel.transpose x) (rel.transpose y))))
(check-sat)
