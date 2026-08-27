; note: cpc reference checking not supported, declare-heap cannot appear in an ethos reference file
; DISABLE-TESTER: cpc
; REQUIRES: unrestricted-mode
(set-logic QF_ALL)
(set-info :status unsat)
(declare-heap (Int Int))

(declare-const x Int)

(declare-const a Int)
(declare-const b Int)

(assert (and (pto x a) (pto x b)))

(assert (not (= a b)))

(check-sat)
