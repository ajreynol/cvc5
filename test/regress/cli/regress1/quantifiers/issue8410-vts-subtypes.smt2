; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
; COMMAND-LINE: -i
; EXPECT: unsat
;; Unary OR is not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(push)
(assert (or (forall ((v Real)) (or (exists ((V Real)) (or (exists ((V Real)) (= 0 (mod (to_int v) (to_int (- v)))))))))))
(check-sat)
