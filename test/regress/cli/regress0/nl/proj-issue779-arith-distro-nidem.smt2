; COMMAND-LINE: --produce-proofs
; EXPECT: (error "Cannot eliminate subtypes from an input assumption with --strict-assumptions. Use --no-strict-assumptions to allow this.")
; EXIT: 1
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-fun a () Int)                                                             
(declare-fun b () Int)                                                             
(assert (< (- a (* b (/ a (- 1)))) (* (- a (+ 1 b)) (/ a (- 1)))))                 
(check-sat)
