; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Subexpressions must have the same type"
; EXPECT: Subexpressions must have the same type
; EXIT: 1
; COMMAND-LINE: --produce-proofs
; Logos rejects scoped assumptions containing free bound variables.
; DISABLE-TESTER: cpc-logos
; DISABLE-TESTER: alethe
(set-logic ALL)
(assert (not (exists ((a Real)) (forall ((b Real)) 
(exists ((c Real)) (exists ((a Real)) (forall ((b Real)) 
(exists ((c Real)) (and (not (= (+ b c) 0))
(xor (not (= a 0)) (> c 0)))))))))))
(check-sat)                    
