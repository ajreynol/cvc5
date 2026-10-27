; COMMAND-LINE: --z3
; EXPECT: unsat
; same shape but the quantifier itself only appears after an instantiation
; DISABLE-TESTER: unsat-core
; The unsat core drops the assertions that provide the trigger terms, so
; E-matching answers unknown on the core alone.
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
