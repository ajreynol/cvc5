; note: cpc reference checking not supported, the Relation and Table sort aliases have no Eunoia equivalent, define is not variadic
; DISABLE-TESTER: cpc
; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(assert (= y (rel.join (rel.tclosure x) x)))
(assert (set.member (tuple 1 2) (rel.join (rel.join x x) x)))
(assert (not (set.subset y (rel.tclosure x))))
(check-sat)
