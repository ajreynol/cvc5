; COMMAND-LINE: --z3 --incremental --z3-prop-engine=z3
; EXPECT: unknown
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; The first check saturates E-matching without refuting the quantifier, so it
; is unknown rather than sat: --z3 has no model based instantiation and must
; not claim satisfiability here.
; Only the port's own search: under cvc5's prop engine, the core does not
; match the quantifier against the term of the second check (incremental
; use is not a goal there).
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun a () U)
(assert (forall ((x U)) (= (f x) a)))
(check-sat)
(assert (not (= (f a) a)))
(check-sat)
