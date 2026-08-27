; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
; EXPECT: unsat
(set-logic ALL)
(declare-fun a () Int)                                                             
(declare-fun b () Int)                                                             
(assert (> b 0))                                                                   
(assert (not (= (/ (* a b) b) a)))                                                 
(check-sat)  
