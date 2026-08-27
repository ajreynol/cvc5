; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
(set-logic QF_RDL)
(set-info :status unsat)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (not (=> (< (- x y) 0) (< x y))))
(check-sat)

