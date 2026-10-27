; COMMAND-LINE: --z3
; EXPECT: unsat
; Outside of incremental mode, the assumptions of check-sat-assuming are
; preprocessed and prepared with the assertions.
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) Bool)
(declare-fun a () U)
(assert (forall ((x U)) (! (f x) :pattern ((f x)))))
(check-sat-assuming ((not (f a))))
