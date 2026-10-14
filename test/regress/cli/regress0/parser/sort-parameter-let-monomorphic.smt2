; EXIT: 1
; DISABLE-TESTER: dump
; SCRUBBER: grep -o 'Type ascription not satisfied'
; EXPECT: Type ascription not satisfied
(set-logic UFLIA)
(declare-sort-parameter A)
(declare-const c A)
; Global c can be instantiated; its local alias cannot.
(assert (let ((alias c)) (= (as alias Int) 0)))
