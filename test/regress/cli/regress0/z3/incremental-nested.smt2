; COMMAND-LINE: --z3 --incremental --no-e-matching
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
; Assertions at several user levels, popped one level at a time.
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun p (U) Bool)
(declare-fun a () U)
(push 1)
(assert (forall ((x U)) (! (=> (p x) (p (f x))) :pattern ((f x)))))
(push 1)
(assert (p a))
(push 1)
(assert (not (p (f (f a)))))
(check-sat)
(pop 1)
(assert (not (p (f a))))
(check-sat)
(pop 1)
(pop 1)
(assert (p a))
(assert (not (p (f (f a)))))
(check-sat)
(check-sat)
