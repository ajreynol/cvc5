; note: cpc reference checking not supported, declare-heap cannot appear in an ethos reference file
; DISABLE-TESTER: cpc
; REQUIRES: unrestricted-mode
; COMMAND-LINE: --full-saturate-quant
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-heap (Int Int))

(declare-const u Int)

(assert sep.emp)

(assert 
(forall ((y Int)) 
(not (wand (pto u 5) (and (= y 42) (pto u 5))))
))

(check-sat)
