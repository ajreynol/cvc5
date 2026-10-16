; COMMAND-LINE: --z3
; COMMAND-LINE: --z3 --z3-slots=quantifiers
; COMMAND-LINE: --z3 --z3-slots=quantifiers --no-z3-shadow-plugins
; COMMAND-LINE: --z3 --z3-prop-engine=z3 --z3-preset=z3
; EXPECT: unknown
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; Satisfiable only with model based instantiation, which is not ported. The
; answer must stay unknown: an adapter that lost the incompleteness reason
; would turn this into a wrong "sat".
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun a () U)
(declare-fun p (U) Bool)
(assert (forall ((x U)) (! (p (f x)) :pattern ((p x)))))
(assert (p a))
(check-sat)
