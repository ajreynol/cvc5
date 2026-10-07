; COMMAND-LINE: --eager-inst --eager-inst-output=lemma --no-e-matching
; EXPECT: unsat
; Exercises pattern inference: no annotation is given, so the patterns are the
; ones z3's pattern_inference would infer, here (f x) and the multi-pattern
; ((f x) (h y)).
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun h (U) U)
(declare-fun k (U U) U)
(declare-fun p (U) Bool)
(declare-fun a () U)
(declare-fun b () U)
(assert (forall ((x U)) (p (f x))))
(assert (forall ((x U) (y U)) (= (k (f x) (h y)) (f x))))
(assert (not (p (k (f a) (h b)))))
(check-sat)
