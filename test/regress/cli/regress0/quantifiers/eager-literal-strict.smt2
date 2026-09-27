; REQUIRES: unrestricted-mode
; COMMAND-LINE: --eager-inst-literal --no-e-matching --no-cbqi --user-pat=strict
; EXPECT: unknown
(set-logic UF)
(declare-sort U 0)
(declare-const a U)
(declare-fun P (U) Bool)
(declare-fun Q (U) Bool)
(declare-fun T (U) Bool)
; A body predicate is not permission to replace an unrelated strict pattern.
(assert (forall ((x U)) (! (or (not (P x)) (Q x)) :pattern ((T x)))))
(assert (P a))
(assert (not (Q a)))
(check-sat)
