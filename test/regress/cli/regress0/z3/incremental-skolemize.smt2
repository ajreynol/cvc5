; COMMAND-LINE: --z3 --incremental --no-e-matching
; EXPECT: unsat
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
; The skolemization of a quantified formula asserted false, again in a new
; user scope. The unsat-core tester's check of the core answers unknown, as
; it does outside of incremental mode.
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) Bool)
(declare-fun g (U) Bool)
(push 1)
(assert (not (forall ((x U)) (! (f x) :pattern ((f x))))))
(assert (forall ((x U)) (! (f x) :pattern ((g x)))))
(assert (forall ((x U)) (! (g x) :pattern ((f x)))))
(check-sat)
(pop 1)
(push 1)
(assert (not (forall ((x U)) (! (f x) :pattern ((f x))))))
(assert (forall ((x U)) (! (f x) :pattern ((g x)))))
(assert (forall ((x U)) (! (g x) :pattern ((f x)))))
(check-sat)
(pop 1)
