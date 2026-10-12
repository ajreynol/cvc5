; COMMAND-LINE: --z3
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (= x (bvadd x #b0001)))
(check-sat)
