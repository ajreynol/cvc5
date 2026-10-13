; DISABLE-TESTER: dump
; SCRUBBER: grep -o "Symbol 'A' previously declared as a type"
; EXPECT: Symbol 'A' previously declared as a type
; EXIT: 1
(set-logic ALL)
(declare-sort A 0)
(declare-sort-parameter A)
