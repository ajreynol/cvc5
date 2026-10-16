; COMMAND-LINE: --z3
; COMMAND-LINE: --z3 --z3-slots=quantifiers
; COMMAND-LINE: --z3 --z3-slots=quantifiers --no-z3-shadow-plugins
; COMMAND-LINE: --z3 --z3-prop-engine=z3 --z3-preset=z3
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
