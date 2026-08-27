; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
(set-logic QF_LRA)
(set-info :status unsat)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (not (=> (and (> x 0) (< (* 2 x) y)) (and (> y 0) (< x y)))))
(check-sat)
