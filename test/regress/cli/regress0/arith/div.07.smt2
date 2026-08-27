; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun n () Real)

(assert (= (/ x n) 0))
(assert (= (/ y (/ x n)) 1))
(assert (<= n 0))
(assert (>= n 0))
(assert (= x y))

(check-sat)
