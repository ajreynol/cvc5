; COMMAND-LINE: --arith-int-repair
; COMMAND-LINE: --arith-int-repair --no-dio-solver
; COMMAND-LINE: --no-arith-int-repair
; REQUIRES: unrestricted-mode
; EXPECT: unsat
; No feasible integer repair exists. DIO or branch-and-bound must still run.
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (>= (+ (* 2 x) (* 3 y)) 1))
(assert (<= (+ (* 2 x) (* 3 y)) 1))
(assert (>= y 0))
(assert (<= y 0))
(check-sat)
