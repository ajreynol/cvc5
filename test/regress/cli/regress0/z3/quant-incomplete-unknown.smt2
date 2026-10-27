; COMMAND-LINE: --z3 --no-e-matching
; EXPECT: unknown
; Satisfiable only with model based instantiation, which is not ported. The
; answer must stay unknown: an adapter that lost the incompleteness reason
; would turn this into a wrong "sat". cvc5's E-matching, which instantiates
; without bound here, is off.
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun a () U)
(declare-fun p (U) Bool)
(assert (forall ((x U)) (! (p (f x)) :pattern ((p x)))))
(assert (p a))
(check-sat)
