; COMMAND-LINE: --z3 --produce-models
; EXPECT: (error "Error in option parsing: --produce-models is not supported with --z3")
; EXIT: 1
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: dump
; The supported surface of --z3 is deliberately minimal; see
; src/z3/README.md. Refusing is the point: answering would use cvc5's
; own engines, which --z3 leaves constructed but inactive and which
; have therefore seen none of the assertions.
(set-logic UF)
(declare-sort U 0)
(declare-fun a () U)
(assert (distinct a a))
(check-sat)
