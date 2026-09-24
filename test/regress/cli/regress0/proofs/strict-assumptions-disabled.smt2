; COMMAND-LINE: --produce-proofs --no-strict-assumptions
; EXPECT: sat
(set-logic ALL)
(define-fun f ((i Int)) Real (+ i 0.5))
(define-const c Real (/ 0.0 0))
(declare-const i Int)
(assert (< i (f i)))
(check-sat)
