; COMMAND-LINE: --z3 --incremental --no-e-matching
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; The assumptions of check-sat-assuming are asserted in an internal user scope.
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) Bool)
(declare-fun a () U)
(declare-fun b () U)
(assert (forall ((x U)) (! (f x) :pattern ((f x)))))
(check-sat-assuming ((not (f a))))
(check-sat-assuming ((not (f b))))
(push 1)
(check-sat-assuming ((not (f a))))
(pop 1)
