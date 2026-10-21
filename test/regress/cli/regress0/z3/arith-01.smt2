; COMMAND-LINE: --z3
; EXPECT: unsat
; DISABLE-TESTER: model
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
