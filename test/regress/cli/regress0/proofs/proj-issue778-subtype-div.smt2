; COMMAND-LINE: --produce-proofs
; EXPECT: (error "Cannot eliminate subtypes from an input assumption with --strict-assumptions. Use --no-strict-assumptions to allow this.")
; EXIT: 1
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-const a Real) 
(assert (> (/ (abs 2) a a) (+ (/ 2 a a) 1.0))) 
(check-sat)        
