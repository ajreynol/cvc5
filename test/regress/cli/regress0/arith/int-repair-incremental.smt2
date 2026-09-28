; COMMAND-LINE: --arith-int-repair --incremental
; COMMAND-LINE: --no-arith-int-repair --incremental
; REQUIRES: unrestricted-mode
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; Repair must respect new bounds and disequalities and survive their removal.
(set-logic QF_LIRA)
(declare-const x Int)
(declare-const y Real)
(assert (and (>= x 0) (<= x 3) (> y 0) (< y 1)))
(assert (> (+ (* 2 x) y) 1))
(assert (< (+ (* 2 x) y) 3))
(check-sat)
(push 1)
(assert (<= (+ (* 2 x) y) 2))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (distinct y (/ 1 2)))
(check-sat)
(assert (distinct x 1))
(check-sat)
(pop 1)
(check-sat)
