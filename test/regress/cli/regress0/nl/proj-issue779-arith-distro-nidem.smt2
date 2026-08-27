; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-fun a () Int)                                                             
(declare-fun b () Int)                                                             
(assert (< (- a (* b (/ a (- 1)))) (* (- a (+ 1 b)) (/ a (- 1)))))                 
(check-sat)
