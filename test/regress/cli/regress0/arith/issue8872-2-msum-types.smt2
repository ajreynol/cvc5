; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Subexpressions must have the same type"
; EXPECT: Subexpressions must have the same type
; EXIT: 1
; REQUIRES: unrestricted-mode
; COMMAND-LINE: --ext-rew-prep=agg
(set-logic ALL)
(declare-fun v () Bool)
(declare-fun a () Real)
(declare-fun va () Real)
(assert (= (- a va) (ite v 0 1)))
(check-sat)
