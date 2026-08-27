; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic QF_NRAT)
(assert (= 0.0 (sin 7)))
(check-sat)
