; REQUIRES: unrestricted-mode
; COMMAND-LINE: --eager-inst-literal --no-e-matching --no-cbqi --user-pat=strict --sat-solver=cadical
; COMMAND-LINE: --eager-inst-literal --no-e-matching --no-cbqi --user-pat=strict --sat-solver=minisat
; EXPECT: unsat
(set-logic UF)
(declare-sort U 0)
(declare-const a U)
(declare-fun P (U) Bool)
(declare-fun Q (U) Bool)
(declare-fun R (U) Bool)
; Q(a) is initially absent. The first instance must introduce it as a unit.
(assert (forall ((x U)) (! (or (not (P x)) (Q x)) :pattern ((P x)))))
(assert (forall ((x U)) (! (or (not (Q x)) (R x)) :pattern ((Q x)))))
(assert (P a))
(assert (not (R a)))
(check-sat)
