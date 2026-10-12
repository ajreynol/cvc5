; COMMAND-LINE: --z3 --deep-restart=input
; EXPECT: (error "Error in option parsing: --deep-restart is not supported with --z3")
; EXIT: 1
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: dump
; The supported surface of --z3 is deliberately minimal; see
; src/z3/README.md. A deep restart restarts from the literals cvc5's SAT
; solver learned, and with --z3 that solver never searches.
(set-logic UF)
(declare-fun p () Bool)
(assert p)
(check-sat)
