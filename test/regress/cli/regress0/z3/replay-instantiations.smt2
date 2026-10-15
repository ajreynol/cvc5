; REQUIRES: unrestricted-mode
; COMMAND-LINE: --z3 --z3-replay --z3-preset=verus-best --no-e-matching --no-cbqi --no-cegqi --no-enum-inst --no-mbqi --produce-proofs
; COMMAND-LINE: --z3-replay --z3-preset=verus-best --z3-prop-engine=cvc5 --no-e-matching --no-cbqi --produce-proofs
; COMMAND-LINE: --z3-replay --z3-preset=verus-best --z3-theory-engine=cvc5 --no-e-matching --no-cbqi --produce-proofs
; DISABLE-TESTER: unsat-core
; The core checker inherits disabled native instantiation but has no replay hints.
; EXPECT: unsat
; A nontrivial, two-variable instance must come from replay. Neither the
; native instantiation strategies nor ground preprocessing can refute this.
(set-logic UF)
(declare-sort U 0)
(declare-sort V 0)
(declare-fun f (U) U)
(declare-fun g (V) V)
(declare-fun p (U V) Bool)
(declare-const a U)
(declare-const b V)
(assert (forall ((x U) (y V)) (! (p (f x) (g y)) :pattern ((f x) (g y)))))
(assert (not (p (f a) (g b))))
(check-sat)
