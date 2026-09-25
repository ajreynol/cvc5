; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Subexpressions must have the same type"
; EXPECT: Subexpressions must have the same type
; EXIT: 1
(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(assert (= (/ x 0) 6))
(check-sat)
(get-value ((/ x 0)))
