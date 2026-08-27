; note: cpc reference checking not supported, the Relation and Table sort aliases have no Eunoia equivalent, define is not variadic
; DISABLE-TESTER: cpc
; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(assert (= y (rel.tclosure x)))
(assert (not (set.subset (rel.join (rel.join x x) x) y)))
(check-sat)
