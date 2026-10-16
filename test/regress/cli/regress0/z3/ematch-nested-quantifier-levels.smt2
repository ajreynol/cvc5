; COMMAND-LINE: --z3
; COMMAND-LINE: --z3 --z3-slots=quantifiers
; COMMAND-LINE: --z3 --z3-prop-engine=z3 --z3-preset=z3
; COMMAND-LINE: --z3 --z3-prop-engine=z3
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; same shape but the quantifier itself only appears after an instantiation
(set-logic UF)
(declare-sort U 0)
(declare-fun ap (U U) U) (declare-fun g (U) U)
(declare-fun pp () U) (declare-fun a () U)
(declare-fun q (U) Bool) (declare-fun r (U) Bool) (declare-fun s (U) Bool)
(assert (forall ((y U)) (! (forall ((x U)) (! (q x) :pattern ((ap (g y) x)))) :pattern ((s y)))))
(assert (s pp))
(assert (r (ap pp a)))
(assert (= pp (g pp)))
(assert (not (q a)))
(check-sat)
