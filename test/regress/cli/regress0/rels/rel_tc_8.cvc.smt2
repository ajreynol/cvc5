; note: cpc reference checking not supported, the Relation and Table sort aliases have no Eunoia equivalent, define is not variadic
; DISABLE-TESTER: cpc
; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(assert (set.member (tuple 2 2) (rel.tclosure x)))
(assert (= x (as set.empty (Relation Int Int))))
(check-sat)
