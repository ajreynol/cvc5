; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-const a Real) 
(assert (> (/ (abs 2) a a) (+ (/ 2 a a) 1.0))) 
(check-sat)        
