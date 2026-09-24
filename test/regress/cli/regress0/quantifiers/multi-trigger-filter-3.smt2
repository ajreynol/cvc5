; COMMAND-LINE: --no-cbqi --no-enum-inst
; The filter term (g a) for the multi-trigger in the second quantified formula
; only exists after instantiating the first quantified formula.
(set-logic UF)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun f (U U) U)
(declare-fun g (U) U)
(declare-fun R (U) Bool)
(declare-fun a () U)
(declare-fun b () U)
(assert (forall ((x U)) (! (= (g x) x) :pattern ((R x)))))
(assert (forall ((x U) (y U)) (! (= (f x y) y) :pattern ((f x y) (g x)))))
(assert (R a))
(assert (not (= (f a b) b)))
(check-sat)
