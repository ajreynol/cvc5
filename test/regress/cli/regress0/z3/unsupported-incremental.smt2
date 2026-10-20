; COMMAND-LINE: --z3 --incremental
; EXPECT: (error "Error in option parsing: --incremental is not supported with --z3")
; EXIT: 1
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: dump
; The ported core does not follow user scopes (push, pop, the assumptions of
; check-sat-assuming) or answer more than one check-sat.
(set-logic UF)
(declare-fun p () Bool)
(push 1)
(assert p)
(check-sat)
(pop 1)
