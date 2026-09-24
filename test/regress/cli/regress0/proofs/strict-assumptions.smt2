; COMMAND-LINE: --produce-proofs
; COMMAND-LINE: --produce-proofs --strict-assumptions
; EXPECT: (error "Cannot eliminate subtypes from an input assumption with --strict-assumptions. Use --no-strict-assumptions to allow this.")
; EXIT: 1
(set-logic ALL)
(declare-const i Int)
(declare-const r Real)
(assert (< i r))
(check-sat)
