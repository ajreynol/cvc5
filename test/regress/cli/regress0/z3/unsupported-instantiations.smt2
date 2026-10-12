; COMMAND-LINE: --z3 --dump-instantiations
; EXPECT: (error "Error in option parsing: --dump-instantiations is not supported with --z3")
; EXIT: 1
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: dump
; The supported surface of --z3 is deliberately minimal; see
; src/z3/README.md. The port does its own instantiation, so cvc5's
; quantifiers engine, which would answer this, has made none; before this was
; refused it printed "none" for this problem.
(set-logic UF)
(declare-sort U 0)
(declare-fun P (U) Bool)
(declare-fun a () U)
(assert (forall ((x U)) (! (P x) :pattern ((P x)))))
(assert (not (P a)))
(check-sat)
