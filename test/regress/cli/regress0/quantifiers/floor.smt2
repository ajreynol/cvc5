; COMMAND-LINE: --produce-proofs
; EXPECT: (error "Cannot eliminate subtypes from an input assumption with --strict-assumptions. Use --no-strict-assumptions to allow this.")
; EXIT: 1
(set-logic LIRA)
(set-info :status unsat)
(assert (forall ((X Real)) (not (>= (+ (to_int (* 2 X)) (* (- 2) (to_int X))) 1)) ))
(check-sat)