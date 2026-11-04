; COMMAND-LINE: --eager-e-matching --incremental --no-e-matching --no-quant-alpha-equiv
; EXPECT: unknown
; EXPECT: unsat
; The quantified formula of the second scope is alpha-equivalent to the one of
; the first, so the core has the same form for both; after the pop, its
; instances must be of the formula asserted now, not of the popped one.
(set-logic UF)
(declare-sort U 0)
(declare-fun P (U) Bool)
(declare-fun a () U)
(push 1)
(assert (forall ((x U)) (! (P x) :pattern ((P x)))))
(check-sat)
(pop 1)
(push 1)
(assert (forall ((y U)) (! (P y) :pattern ((P y)))))
(assert (not (P a)))
(check-sat)
(pop 1)
