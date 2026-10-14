; COMMAND-LINE: --strict-parsing
; EXIT: 1
; DISABLE-TESTER: dump
; SCRUBBER: grep -o 'Ambiguous polymorphic symbol requires an (as ... sort) qualifier'
; EXPECT: Ambiguous polymorphic symbol requires an (as ... sort) qualifier
(set-logic UFLIA)
(declare-sort-parameter A)
(declare-const c A)
(assert (= c c))
