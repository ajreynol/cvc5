; COMMAND-LINE: --z3
; COMMAND-LINE: --z3 --z3-slots=quantifiers
; COMMAND-LINE: --z3 --z3-slots=quantifiers --no-z3-shadow-plugins
; COMMAND-LINE: --z3 --z3-prop-engine=z3 --z3-preset=z3
; COMMAND-LINE: --z3 --z3-prop-engine=z3
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
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
