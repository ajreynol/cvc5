; COMMAND-LINE: --eager-e-matching --incremental --check-proofs
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; The instance for a, made under a decision and weakened by it, and the
; definition of the skolem of its ite, are made again in each user scope,
; where cvc5's preprocessing gives them again, with their proofs.
(set-logic UFLIA)
(set-option :produce-proofs true)
(declare-sort U 0)
(declare-fun P (Int) Bool)
(declare-fun Q (U) Bool)
(declare-fun f (U) Int)
(declare-fun a () U)
(declare-fun R () Bool)
(declare-fun T () Bool)
(assert (forall ((x U)) (! (P (ite (Q x) (f x) 0)) :pattern ((f x)))))
(push 1)
(assert (Q a))
(assert (or R T))
(assert (=> R (not (P (f a)))))
(assert (=> T (not (P (f a)))))
(check-sat)
(pop 1)
(push 1)
(assert (Q a))
(assert (or R T))
(assert (=> R (not (P (f a)))))
(assert (=> T (not (P (f a)))))
(check-sat)
(pop 1)
(push 1)
(assert (Q a))
(assert (or R T))
(assert (=> R (not (P (f a)))))
(assert (=> T (not (P (f a)))))
(check-sat)
(pop 1)
