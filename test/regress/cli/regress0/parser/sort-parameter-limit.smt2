; COMMAND-LINE: --sort-inst-limit=1
; EXPECT: unknown
(set-logic UFLIA)
(declare-sort-parameter A)
(declare-const c A)
(declare-fun p (A) Bool)
(assert (p c))
(check-sat)
