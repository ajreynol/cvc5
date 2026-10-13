; COMMAND-LINE: --strict-parsing
; EXPECT: sat
; EXPECT: (
; EXPECT: )
; Parameters do not require free sorts in the logic and are not model sorts.
(set-logic QF_LIA)
(set-option :produce-models true)
(declare-sort-parameter |A B|)
(check-sat)
(get-model)
