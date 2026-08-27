; note: cpc reference checking not supported, declare-heap cannot appear in an ethos reference file
; DISABLE-TESTER: cpc
; REQUIRES: unrestricted-mode
(set-logic QF_ALL)
(set-info :status unsat)
(declare-heap (Int Int))

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(declare-const a Int)
(declare-const b Int)

(assert (not (sep true (pto x a))))
(assert (sep (pto x a) (pto z b)))


(check-sat)
