; COMMAND-LINE: --produce-proofs
; EXPECT: (error "Cannot eliminate subtypes from an input assumption with --strict-assumptions. Use --no-strict-assumptions to allow this.")
; EXIT: 1
; Logos rejects scoped assumptions containing free bound variables.
; DISABLE-TESTER: cpc-logos
; DISABLE-TESTER: alethe
(set-logic ALL)
(assert (not (exists ((a Real)) (forall ((b Real)) 
(exists ((c Real)) (exists ((a Real)) (forall ((b Real)) 
(exists ((c Real)) (and (not (= (+ b c) 0))
(xor (not (= a 0)) (> c 0)))))))))))
(check-sat)                    
