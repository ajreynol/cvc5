; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Subexpressions must have the same type"
; EXPECT: Subexpressions must have the same type
; EXIT: 1
; COMMAND-LINE: --no-strict-parsing
(set-logic ALL)
(set-info :status sat)
(declare-fun x () Real)
(assert (= x 10))
(assert (<= (+ x 1) 20))
(check-sat)
