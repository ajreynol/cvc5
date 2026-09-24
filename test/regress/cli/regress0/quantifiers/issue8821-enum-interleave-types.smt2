; EXPECT: (error "Cannot eliminate subtypes from an input assumption with --strict-assumptions. Use --no-strict-assumptions to allow this.")
; EXIT: 1
; COMMAND-LINE: --produce-proofs --enum-inst-interleave
(set-logic ALL)
(assert (forall ((a Real)) (or (> 0 a) (> a 0.0))))
(check-sat)
