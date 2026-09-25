; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Subexpressions must have the same type"
; EXPECT: Subexpressions must have the same type
; EXIT: 1
; REQUIRES: unrestricted-mode
; COMMAND-LINE: --sygus-inference=try
(set-logic ALL)
(declare-fun x () Real)
(assert (= x 1))
(assert (= (sqrt x) x))
(check-sat)
