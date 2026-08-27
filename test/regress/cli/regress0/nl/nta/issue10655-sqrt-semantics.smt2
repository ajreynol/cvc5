; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic QF_NRAT)
(declare-fun x () Real)
(assert (>= x 0))
(assert (< (sqrt x) 0))
(check-sat)
