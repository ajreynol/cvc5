; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Subexpressions must have the same type"
; EXPECT: Subexpressions must have the same type
; EXIT: 1
(set-logic ALL)
(declare-fun a () Int)                                                             
(declare-fun b () Int)                                                             
(assert (> b 0))                                                                   
(assert (not (= (/ (* a b) b) a)))                                                 
(check-sat)  
