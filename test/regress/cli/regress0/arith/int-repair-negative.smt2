; COMMAND-LINE: --arith-int-repair
; COMMAND-LINE: --no-arith-int-repair
; REQUIRES: unrestricted-mode
; EXPECT: sat
; Repair a negative fractional assignment by changing a nonbasic row sum.
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (and (>= x (- 3)) (<= x 0) (>= y (- 3)) (<= y 0)))
(assert (>= (+ (* 2 x) y) (- 5)))
(assert (<= (+ (* 2 x) y) (- 1)))
(check-sat)
