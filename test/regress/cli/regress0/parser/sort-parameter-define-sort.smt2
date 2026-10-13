; DISABLE-TESTER: dump
; SCRUBBER: grep -o "Global sort parameters are not permitted in define-sort"
; EXPECT: Global sort parameters are not permitted in define-sort
; EXIT: 1
(set-logic ALL)
(declare-sort-parameter A)
; A global parameter cannot be captured by a sort abbreviation.
(define-sort Alias () (Array Int A))
