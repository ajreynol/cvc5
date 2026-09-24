; DISABLE-TESTER: dump
; COMMAND-LINE: --produce-proofs
; EXPECT: (error "Cannot eliminate subtypes from an input assumption with --strict-assumptions. Use --no-strict-assumptions to allow this.")
; EXIT: 1
(set-logic ALL)
(define-fun f ((i Int)) Real (+ i 0.5))
(check-sat)
