; COMMAND-LINE: --incremental
; DISABLE-TESTER: dump
; EXPECT: sat
; EXPECT: unknown
; EXPECT: sat
(set-logic UF)
(declare-sort-parameter A)
(declare-const c A)
(declare-fun p (A) Bool)
(assert (p c))
(check-sat)
(push 1)
(declare-sort Box 1)
(check-sat)
(pop 1)
(check-sat)
