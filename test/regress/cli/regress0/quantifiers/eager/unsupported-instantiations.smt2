; COMMAND-LINE: --eager-e-matching --dump-instantiations
; EXPECT: (error "Error in option parsing: --dump-instantiations without --produce-proofs is not supported with --eager-e-matching")
; EXIT: 1
; The supported surface of --eager-e-matching is deliberately minimal; see
; src/theory/quantifiers/eager/README.md. The core does its own instantiation, which cvc5's
; quantifiers engine does not record; the instantiations are read from the
; proof with --produce-proofs.
(set-logic UF)
(declare-sort U 0)
(declare-fun P (U) Bool)
(declare-fun a () U)
(assert (forall ((x U)) (! (P x) :pattern ((P x)))))
(assert (not (P a)))
(check-sat)
