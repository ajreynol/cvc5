; COMMAND-LINE: --z3 --deep-restart=input
; EXPECT: (error "Error in option parsing: --deep-restart is not supported with --z3")
; EXIT: 1
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: dump
; The supported surface of --z3 is deliberately minimal; see
; src/z3/README.md. A deep restart makes a new prop engine from the literals
; learned at level zero, while the core keeps the state of the previous
; search.
(set-logic UF)
(declare-fun p () Bool)
(assert p)
(check-sat)
