; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
; REQUIRES: unrestricted-mode
(set-logic QF_NRAT)
(assert (> (cot 0.0) (/ 1 0)))
(set-info :status unsat)
(check-sat)
