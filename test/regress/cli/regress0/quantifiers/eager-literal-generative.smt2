; REQUIRES: unrestricted-mode
; COMMAND-LINE: --eager-inst-literal --no-e-matching --no-cbqi --user-pat=strict
; EXPECT: unknown
(set-logic UFLIA)
(declare-fun Q (Int) Bool)
; This would generate Q(1), Q(2), ... eagerly without the unit restriction.
(assert (forall ((x Int)) (! (or (not (Q x)) (Q (+ x 1))) :pattern ((Q x)))))
(assert (Q 0))
(assert (not (Q 3)))
(check-sat)
