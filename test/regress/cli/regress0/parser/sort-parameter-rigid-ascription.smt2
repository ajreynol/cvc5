; EXIT: 1
; DISABLE-TESTER: dump
; SCRUBBER: grep -o "requested sort is not an instance of the symbol's sort"
; EXPECT: requested sort is not an instance of the symbol's sort
(set-logic UF)
(declare-sort-parameter A)
(declare-sort-parameter B)
(declare-fun id (A) A)
(assert (forall ((x B)) (= ((as id A) x) x)))
