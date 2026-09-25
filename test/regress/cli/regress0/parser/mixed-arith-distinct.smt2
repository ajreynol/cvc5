; DISABLE-TESTER: dump
; REQUIRES: no-competition
; COMMAND-LINE:
; COMMAND-LINE: --no-strict-parsing
; COMMAND-LINE: --strict-parsing
; SCRUBBER: grep -o "Not all arguments are of the same type"
; EXPECT: Not all arguments are of the same type
; EXIT: 1
(set-logic ALL)
(declare-const i Int)
(declare-const r Real)
(assert (distinct i i r))
(check-sat)
