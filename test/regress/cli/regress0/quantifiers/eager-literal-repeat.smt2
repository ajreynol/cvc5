; REQUIRES: unrestricted-mode
; COMMAND-LINE: --incremental --eager-inst-literal --no-e-matching --no-cbqi --user-pat=strict --sat-solver=cadical
; COMMAND-LINE: --incremental --eager-inst-literal --no-e-matching --no-cbqi --user-pat=strict --sat-solver=minisat
; EXPECT: unknown
; EXPECT: unsat
(set-logic UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-fun P (U U) Bool)
(declare-fun Q (U) Bool)
(assert (distinct a b))
(assert (forall ((x U)) (! (or (not (P x x)) (Q x)) :pattern ((P x x)))))
(assert (not (Q a)))
(push 1)
; Repeated variables must agree syntactically; P(a,b) cannot bind x twice.
(assert (P a b))
(check-sat)
(pop 1)
(push 1)
(assert (P a a))
(check-sat)
(pop 1)
