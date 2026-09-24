; EXPECT: (error "Cannot eliminate subtypes from an input assumption with --strict-assumptions. Use --no-strict-assumptions to allow this.")
; EXIT: 1
; COMMAND-LINE: --check-proofs --tlimit-per=1000
(set-logic ALL)
(assert
 (forall ((x Int) (y Int) (a Real) (z Int))
  (or (> 0.0 (* (/ x y) (/ (* y 2) 0.0)))
      (< 0.0 (/ a 2 y (/ (* z z) (to_real x)))))))
(check-sat)
