; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
; DISABLE-TESTER: alethe
; COMMAND-LINE: --check-proofs
; EXPECT: unsat
(set-logic ALL)
(define-fun i () Real (/ 0.0 0))
(assert (forall ((l Real)) (and false (= i 0))))
(check-sat)
