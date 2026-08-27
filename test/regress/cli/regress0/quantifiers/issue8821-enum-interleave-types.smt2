; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
; COMMAND-LINE: --enum-inst-interleave
; EXPECT: unsat
(set-logic ALL)
(assert (forall ((a Real)) (or (> 0 a) (> a 0.0))))
(check-sat)
