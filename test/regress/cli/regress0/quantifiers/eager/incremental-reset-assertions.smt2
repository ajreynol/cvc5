; COMMAND-LINE: --eager-e-matching --incremental --no-e-matching
; EXPECT: unsat
; EXPECT: sat
; EXPECT: unsat
; reset-assertions pops the SAT context to level 0, which remakes the core.
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) Bool)
(declare-fun a () U)
(assert (forall ((x U)) (! (f x) :pattern ((f x)))))
(assert (not (f a)))
(check-sat)
(reset-assertions)
(declare-sort U 0)
(declare-fun f (U) Bool)
(declare-fun a () U)
(assert (not (f a)))
(check-sat)
(assert (forall ((x U)) (! (f x) :pattern ((f x)))))
(check-sat)
