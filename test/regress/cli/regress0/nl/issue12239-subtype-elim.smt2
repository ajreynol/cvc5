; COMMAND-LINE: --produce-proofs
; EXPECT: (error "Cannot eliminate subtypes from an input assumption with --strict-assumptions. Use --no-strict-assumptions to allow this.")
; EXIT: 1
(set-logic ALL)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (or (< y 0) (< y 0)))
(assert (=> (>= (to_real 0) (* x y)) (>= (to_real 0) (* x y))))
(assert (< (* x x) (* x (to_real (to_int (- x))))))
(check-sat)
