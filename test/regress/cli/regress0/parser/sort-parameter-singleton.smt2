; SCRUBBER: grep -o "Reasoning with global sort parameters is not supported"
; EXPECT: Reasoning with global sort parameters is not supported
; EXIT: 1
; SMT-LIB 2.7, Remark 14: this is UNSAT since A includes Bool.
; An uninterpreted singleton sort would instead be satisfiable.
; Until polymorphic reasoning is implemented, reject rather than report sat.
(set-logic UF)
(declare-sort-parameter A)
(assert (forall ((x A) (y A)) (= x y)))
(check-sat)
