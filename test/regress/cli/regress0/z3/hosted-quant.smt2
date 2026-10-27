; COMMAND-LINE: --z3
; EXPECT: unsat
; cvc5's prop engine over the ported Z3 theory engine: instances made during
; the theory side's propagation reach cvc5 as lemmas, and the chain of two
; instances refutes the ground assertions
(set-logic UFLIA)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun p (U) Bool)
(declare-fun a () U)
(assert (forall ((x U)) (! (=> (p x) (p (f x))) :pattern ((f x)))))
(assert (p a))
(assert (or (not (p (f (f a)))) (= a (f a))))
(assert (not (p (f a))))
(check-sat)
