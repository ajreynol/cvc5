; COMMAND-LINE: --force-logic=UFLIRA
; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Subexpressions must have the same type"
; EXPECT: Subexpressions must have the same type
; EXIT: 1
(declare-sort $$unsorted 0)
(assert (not (forall ((X Int)) (= (* X X) (to_real 1)))))
(set-info :filename scrub.09)
(check-sat-assuming ( true ))
