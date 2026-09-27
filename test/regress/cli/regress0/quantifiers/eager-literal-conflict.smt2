; REQUIRES: unrestricted-mode
; COMMAND-LINE: --eager-inst-literal --no-e-matching --no-cbqi --user-pat=strict --sat-solver=cadical
; COMMAND-LINE: --eager-inst-literal --no-e-matching --no-cbqi --user-pat=strict --sat-solver=minisat
; EXPECT: unsat
(set-logic UF)
(declare-sort U 0)
(declare-const a U)
(declare-fun P (U) Bool)
(declare-fun Q (U) Bool)
(assert (forall ((x U)) (! (or (not (P x)) (Q x)) :pattern ((P x)))))
(assert (P a))
(assert (not (Q a)))
(check-sat)
