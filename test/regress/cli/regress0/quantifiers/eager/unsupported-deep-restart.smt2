; COMMAND-LINE: --eager-e-matching --deep-restart=input
; EXPECT: (error "Error in option parsing: --deep-restart is not supported with --eager-e-matching")
; EXIT: 1
; The supported surface of --eager-e-matching is deliberately minimal; see
; src/theory/quantifiers/eager/README.md. A deep restart makes a new prop engine from the literals
; learned at level zero, while the core keeps the state of the previous
; search.
(set-logic UF)
(declare-fun p () Bool)
(assert p)
(check-sat)
