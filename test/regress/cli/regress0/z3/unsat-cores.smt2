; COMMAND-LINE: --z3 --produce-unsat-cores
; EXPECT: unsat
; EXPECT: (
; EXPECT: q
; EXPECT: nb
; EXPECT: )
; DISABLE-TESTER: model
; DISABLE-TESTER: dump
; DISABLE-TESTER: unsat-core
; The core leaves out (r (f a c)): the instance of q for b and c, which
; E-matching finds through it, refutes (not (p (f b c))) on its own. Without
; that term, E-matching does not find the instance, so checking the core
; (--check-unsat-cores) answers unknown.
(set-logic UF)
(declare-sort U 0) (declare-fun f (U U) U) (declare-fun h (U) U)
(declare-fun a () U) (declare-fun b () U) (declare-fun c () U)
(declare-fun p (U) Bool) (declare-fun r (U) Bool)
(assert (! (forall ((x U) (y U)) (! (p (f x y)) :pattern ((f (h x) y)))) :named q))
(assert (! (= a (h b)) :named ab))
(assert (! (r (f a c)) :named rt))
(assert (! (not (p (f b c))) :named nb))
(check-sat)
(get-unsat-core)
