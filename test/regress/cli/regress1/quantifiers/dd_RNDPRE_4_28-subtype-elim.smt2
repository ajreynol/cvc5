; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
; EXPECT: unsat
(set-logic ALL)
(declare-const x1 Bool)
(assert (forall ((? Real)) (exists ((x Real)) (and x1 (< ? 0)))))
(check-sat)
