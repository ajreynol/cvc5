; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Subexpressions must have the same type"
; EXPECT: Subexpressions must have the same type
; EXIT: 1
; COMMAND-LINE: --check-proofs --proof-check=eager --sat-solver=minisat
(set-logic ALL)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert
 (or (= (div (- (* z (- 1)) 1) 2)
        (* (- z 1) (- z 1) (- x (* x y)) (- x (* x y))))
     (= (div 0 z) (/ z 1))))
(check-sat)
