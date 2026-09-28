; COMMAND-LINE: --arith-int-repair
; COMMAND-LINE: --no-arith-int-repair
; REQUIRES: unrestricted-mode
; EXPECT: sat
; Strict real bounds require retaining the infinitesimal in affected rows.
(set-logic QF_LIRA)
(declare-const x Int)
(declare-const y Real)
(assert (and (>= x 0) (<= x 3) (> y 0) (< y 1)))
(assert (> (+ (* 2 x) y) 1))
(assert (< (+ (* 2 x) y) 3))
(check-sat)
