; REQUIRES: unrestricted-mode
; COMMAND-LINE: --eager-e-matching --no-proof-allow-trust
; EXPECT: unsat
; The nested quantified formula of the instance for a is alpha-equivalent to
; the one in the first assertion, so the core has the same form for both; it
; must still send cvc5 the instance as cvc5's preprocessing gave it, which has
; a proof, rather than its own form renamed back to the first assertion's.
(set-logic UF)
(declare-sort U 0)
(declare-fun P (U) Bool)
(declare-fun Q (U) Bool)
(declare-fun R () Bool)
(declare-fun a () U)
(declare-fun b () U)
(assert (or R (forall ((r U)) (! (P r) :pattern ((P r))))))
(assert (forall ((x U)) (! (or (Q x) (forall ((s U)) (! (P s) :pattern ((P s))))) :pattern ((Q x)))))
(assert (not (Q a)))
(assert (not (P b)))
(check-sat)
