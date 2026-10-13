; DISABLE-TESTER: dump
; SCRUBBER: grep -o "shadowing a theory function symbol"
; EXPECT: shadowing a theory function symbol
; EXIT: 1
(set-logic ALL)
(declare-sort-parameter +)
