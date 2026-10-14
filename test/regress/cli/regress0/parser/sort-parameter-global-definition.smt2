; COMMAND-LINE: --incremental --global-declarations
; DISABLE-TESTER: dump
; EXPECT: unsat
; EXPECT: unsat
(set-logic UFLIA)
(declare-sort-parameter A)
(push 1)
(define-fun id ((x A)) A x)
(pop 1)
(assert (not (= (id 0) 0)))
(check-sat)
(reset-assertions)
(assert (not (id true)))
(check-sat)
