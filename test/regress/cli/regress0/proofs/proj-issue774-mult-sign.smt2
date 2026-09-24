; COMMAND-LINE: --produce-proofs
; EXPECT: (error "Cannot eliminate subtypes from an input assumption with --strict-assumptions. Use --no-strict-assumptions to allow this.")
; EXIT: 1
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-fun s () Real)
(declare-fun k () Real)
(assert (and (< s 1) (<= k 1) (< (div 0 1) s) (= 0.0 (+ 1 (* (- k) s k (- (abs (+ 1 (* s s k (- 1))))))))))
(check-sat)
