; REQUIRES: no-safe-mode
; COMMAND-LINE: --produce-proofs --no-nl-cov
; EXPECT: (error "Cannot eliminate subtypes from an input assumption with --strict-assumptions. Use --no-strict-assumptions to allow this.")
; EXIT: 1
; Input has mixed arithmetic
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-fun s () Real)
(declare-fun k () Real)
(assert (and (< s 1) (<= k 1) (< 0 s) (= 0.0 (+ 1 (* s s k (- 1))))))
(check-sat)
