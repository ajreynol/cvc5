; EXPECT: sat
(set-logic ALL)
(declare-sort-parameter A)
; Local datatype parameters and monomorphic instances still work normally.
(declare-datatypes ((Box 1)) ((par (A) ((box (value A))))))
(define-sort Alias (A) (Box A))
(declare-const b (Alias Int))
(assert (= (value b) 7))
(check-sat)
