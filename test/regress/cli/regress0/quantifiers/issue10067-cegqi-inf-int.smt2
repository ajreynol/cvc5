; REQUIRES: unrestricted-mode
; DISABLE-TESTER: alethe
; COMMAND-LINE: --produce-proofs --cegqi-inf-int --sat-solver=minisat
; EXPECT: (error "Cannot eliminate subtypes from an input assumption with --strict-assumptions. Use --no-strict-assumptions to allow this.")
; EXIT: 1
(set-logic ALL)
(declare-fun a () Real)
(assert
  (forall ((v Int) (r Int))
    (distinct true (>= r (* v (- 1 a) (/ 1 2))))))
(check-sat)
