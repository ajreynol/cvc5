; COMMAND-LINE: --z3
; EXPECT: (error "term pools are not supported with --z3")
; EXIT: 1
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: dump
; The supported surface of --z3 is deliberately minimal; see
; src/z3/README.md. A term pool is used by cvc5's quantifiers engine, which
; takes no part in the port's search.
(set-logic UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-pool L U (a))
(check-sat)
