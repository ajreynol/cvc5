; COMMAND-LINE: --z3
; COMMAND-LINE: --z3 --z3-prop-engine=z3 --z3-preset=z3
; EXPECT: sat
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(check-sat)
