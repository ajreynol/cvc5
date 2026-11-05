; REQUIRES: unrestricted-mode
; COMMAND-LINE: --eager-e-matching --incremental --no-e-matching
; EXPECT: unsat
; EXPECT: unsat
; The core takes the assertions of each check-sat at its scope of their user
; level (without cvc5's E-matching, only the core instantiates).
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) Bool)
(declare-fun a () U)
(declare-fun b () U)
(assert (forall ((x U)) (! (f x) :pattern ((f x)))))
(push 1)
(assert (not (f a)))
(check-sat)
(pop 1)
(push 1)
(assert (not (f b)))
(check-sat)
(pop 1)
