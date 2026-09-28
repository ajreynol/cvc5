; COMMAND-LINE: --arith-int-repair
; COMMAND-LINE: --no-arith-int-repair
; REQUIRES: unrestricted-mode
; EXPECT: sat
; A fractional basic x can be repaired by moving nonbasic y.
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (and (>= x 0) (<= x 3) (>= y 0) (<= y 3)))
(assert (>= (+ (* 2 x) y) 1))
(assert (<= (+ (* 2 x) y) 5))
(check-sat)
