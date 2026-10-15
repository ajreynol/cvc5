; REQUIRES: unrestricted-mode
; COMMAND-LINE: --z3 --z3-replay --z3-preset=verus-best --produce-proofs
; COMMAND-LINE: --z3-replay --z3-preset=verus-best --z3-prop-engine=cvc5 --produce-proofs
; COMMAND-LINE: --z3-replay --z3-preset=verus-best --z3-theory-engine=cvc5 --produce-proofs
; EXPECT: unsat
; Default native instantiation remains enabled; proof and core testers apply.
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
