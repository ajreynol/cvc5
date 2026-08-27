; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
(set-logic LIRA)
(set-info :status unsat)
(assert (forall ((X Real)) (not (>= (+ (to_int (* 2 X)) (* (- 2) (to_int X))) 1)) ))
(check-sat)