; EXPECT: sat
(set-logic QF_UFLIA)
(declare-sort-parameter A)
(declare-fun f (A) A)
; The two ranks denote independent members of one family.
(assert (= (f 0) 1))
(assert (f false))
(check-sat)
