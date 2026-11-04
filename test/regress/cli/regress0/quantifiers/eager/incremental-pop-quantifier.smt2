; COMMAND-LINE: --eager-e-matching --incremental --no-e-matching
; EXPECT: unsat
; EXPECT: sat
; A quantified formula asserted in a popped user scope is gone from the core,
; which would otherwise be in conflict with the remaining assertions.
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) Bool)
(declare-fun a () U)
(push 1)
(assert (forall ((x U)) (! (f x) :pattern ((f x)))))
(assert (not (f a)))
(check-sat)
(pop 1)
(assert (not (f a)))
(check-sat)
