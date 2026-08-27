; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
; REQUIRES: unrestricted-mode
; COMMAND-LINE: --nl-ext-tf-tplanes
; EXPECT: unsat
(set-logic QF_NRAT)
(set-info :status unsat)
(declare-fun x () Real)

(assert (< (sin 1) 0.8414))
(assert (= x (sin 1)))

(check-sat)
