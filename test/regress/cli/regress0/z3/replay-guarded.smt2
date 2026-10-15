; REQUIRES: unrestricted-mode
; COMMAND-LINE: --z3-replay --z3-preset=verus-best --no-e-matching --no-cbqi --produce-proofs
; COMMAND-LINE: --z3-replay --z3-preset=verus-best --z3-theory-engine=cvc5 --no-e-matching --no-cbqi --produce-proofs
; DISABLE-TESTER: unsat-core
; The core checker inherits disabled native instantiation but has no replay hints.
; EXPECT: unsat
; Replay must wait for the guarded quantifier to be asserted by native search.
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) Bool)
(declare-fun fd (U) Bool)
(declare-fun g (U) U)
(declare-fun p (U) Bool)
(declare-fun a () U)
(declare-fun b () U)
; the fuel pattern: a quantifier guarded by a literal that is only made true
; by instantiating another quantifier whose pattern mentions that literal
(assert (or (not (f a)) (forall ((x U)) (! (p x) :pattern ((g x))))))
(assert (forall ((y U)) (! (= (f y) (fd y)) :pattern ((f y)))))
(assert (fd a))
(assert (p (g b)))
(assert (not (p b)))
(check-sat)
