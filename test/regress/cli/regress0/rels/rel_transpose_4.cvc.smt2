; note: cpc reference checking not supported, the Relation and Table sort aliases have no Eunoia equivalent, define is not variadic
; DISABLE-TESTER: cpc
; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(declare-fun z () (Tuple Int Int))
(assert (= z (tuple 1 2)))
(assert (set.member z x))
(assert (not (set.member (tuple 2 1) (rel.transpose x))))
(check-sat)
