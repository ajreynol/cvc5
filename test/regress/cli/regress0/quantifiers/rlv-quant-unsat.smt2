; REQUIRES: unrestricted-mode
; COMMAND-LINE: --rlv-quant=full
; COMMAND-LINE: --rlv-quant=strict
; EXPECT: unsat
; Every asserted quantified formula here is needed to justify the input, so no
; relevance mode may filter any of them and all must still answer unsat.
(set-logic UF)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun P (U) Bool)
(declare-fun Q (U) Bool)
(assert (forall ((x U)) (! (=> (P x) (Q x)) :pattern ((P x)))))
(assert (P a))
(assert (not (Q a)))
(check-sat)
