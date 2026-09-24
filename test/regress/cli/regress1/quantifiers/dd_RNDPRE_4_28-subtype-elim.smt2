; COMMAND-LINE: --produce-proofs
; EXPECT: (error "Cannot eliminate subtypes from an input assumption with --strict-assumptions. Use --no-strict-assumptions to allow this.")
; EXIT: 1
(set-logic ALL)
(declare-const x1 Bool)
(assert (forall ((? Real)) (exists ((x Real)) (and x1 (< ? 0)))))
(check-sat)
