; COMMAND-LINE: --no-cbqi --user-pat=strict --arith-int-repair
; COMMAND-LINE: --no-cbqi --user-pat=strict --no-arith-int-repair
; REQUIRES: unrestricted-mode
; EXPECT: unsat
; The first instance creates a fractional arithmetic model to repair before
; the second quantifier refutes q(a).
(set-logic UFLIA)
(declare-sort U 0)
(declare-const a U)
(declare-fun f (U) Int)
(declare-fun g (U) Int)
(declare-fun p (U) Bool)
(declare-fun q (U) Bool)
(assert (p a))
(assert (forall ((u U)) (! (=> (p u) (and (q u)
  (>= (f u) 0) (<= (f u) 3) (>= (g u) 0) (<= (g u) 3)
  (>= (+ (* 2 (f u)) (g u)) 1) (<= (+ (* 2 (f u)) (g u)) 5)))
  :pattern ((p u)))))
(assert (forall ((u U)) (! (not (q u)) :pattern ((q u)))))
(check-sat)
