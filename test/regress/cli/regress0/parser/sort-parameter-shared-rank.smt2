; EXPECT: unsat
(set-logic UF)
(declare-sort-parameter A)
(declare-sort-parameter B)
(declare-const c A)
(declare-fun p (A) Bool)
(assert (p c))
; Renaming a parameter does not create a new family of symbols.
(assert (not (p (as c B))))
(check-sat)
