; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Subexpressions must have the same type"
; EXPECT: Subexpressions must have the same type
; EXIT: 1
(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (> a 0)) 
(assert (> b 0)) 
(assert (not (= (/ (* a b) (abs b)) a))) 
(check-sat)     
