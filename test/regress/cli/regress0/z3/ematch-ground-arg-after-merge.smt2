; COMMAND-LINE: --z3
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: unsat-core
; pattern with a ground FIRST argument, matched only after a later merge
(set-logic UF)
(declare-sort U 0)
(declare-fun ap (U U) U) (declare-fun g (U) U)
(declare-fun pp () U) (declare-fun a () U)
(declare-fun q (U) Bool) (declare-fun r (U) Bool)
(declare-fun b1 () Bool) (declare-fun b2 () Bool)
(assert (forall ((x U)) (! (q x) :pattern ((ap (g pp) x)))))
(assert (r (ap pp a)))
(assert (or b1 b2))
(assert (or (not b1) (= pp (g pp))))
(assert (or (not b2) (= pp (g pp))))
(assert (not (q a)))
(check-sat)
