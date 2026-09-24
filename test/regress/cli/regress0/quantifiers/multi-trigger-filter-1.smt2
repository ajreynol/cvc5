; COMMAND-LINE: --no-cbqi --no-enum-inst
; Multi-trigger whose second term f(x, y) contains all variables. We match
; f(x, y) only, and use (g x) as a filter, where the filter lookup must
; succeed modulo the equality a = c.
(set-logic UF)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun f (U U) U)
(declare-fun g (U) U)
(declare-fun h (U) U)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(assert (forall ((x U) (y U)) (! (= (f x y) (h y)) :pattern ((g x) (f x y)))))
(assert (= (g c) b))
(assert (= a c))
(assert (not (= (f a b) (h b))))
(check-sat)
