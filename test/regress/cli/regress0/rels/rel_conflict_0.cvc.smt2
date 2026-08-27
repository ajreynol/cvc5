; note: cpc reference checking not supported, the Relation and Table sort aliases have no Eunoia equivalent, define is not variadic
; DISABLE-TESTER: cpc
; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Relation Int Int))
(declare-fun e () (Tuple Int Int))
(assert (= e (tuple 4 4)))
(assert (set.member e x))
(assert (not (set.member (tuple 4 4) x)))
(check-sat)
