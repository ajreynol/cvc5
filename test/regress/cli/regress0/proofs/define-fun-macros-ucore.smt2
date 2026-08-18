; COMMAND-LINE: --proof-define-fun-macros --produce-unsat-cores
; EXPECT: unsat
; EXPECT: (
; EXPECT: )
(set-logic UFLIA)
(define-fun f ((x Int)) Int (+ x 1))
(declare-fun a () Int)
(declare-fun b () Int)
(assert (< (f a) b))
(assert (> a b))
(check-sat)
(get-unsat-core)
