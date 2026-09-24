; EXPECT: (error "Cannot eliminate subtypes from an input assumption with --strict-assumptions. Use --no-strict-assumptions to allow this.")
; EXIT: 1
; COMMAND-LINE: --produce-proofs --incremental
(set-logic ALL)
(declare-fun a () Real)
(declare-fun b () Bool)
(assert (< 0 a))
(assert (xor b (< 0 a 0) false))
(check-sat)
(assert (not b))
(check-sat)
