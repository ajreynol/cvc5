; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
(set-logic NRA)
(set-option :sygus-inst true)

(set-info :status unsat)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(assert (forall ((d Real)) (= (> d 0) (<= (+ d (/ a c)) 0))))
(assert (<= (* b b) 0))
(check-sat)
