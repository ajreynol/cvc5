; REQUIRES: unrestricted-mode
; COMMAND-LINE: --incremental --eager-inst-literal --eager-inst-literal-budget=1 --no-e-matching --no-cbqi --user-pat=strict --sat-solver=cadical
; COMMAND-LINE: --incremental --eager-inst-literal --eager-inst-literal-budget=1 --no-e-matching --no-cbqi --user-pat=strict --sat-solver=minisat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
(set-logic UF)
(declare-sort U 0)
(declare-const a U)
(declare-fun P (U) Bool)
(declare-fun Q (U) Bool)
(assert (P a))
(assert (not (Q a)))
(push 1)
(assert (forall ((x U)) (! (or (not (P x)) (Q x)) :pattern ((P x)))))
(check-sat)
(pop 1)
; Neither the quantifier nor its guarded instance can constrain this scope.
(check-sat)
(push 1)
; Reuse the same rule after popping it; reset the budget for this check-sat.
(assert (forall ((x U)) (! (or (not (P x)) (Q x)) :pattern ((P x)))))
(check-sat)
(pop 1)
(check-sat)
