; COMMAND-LINE: --no-cbqi --no-enum-inst
; EXPECT: unknown
; The filter (g a) does not exist (only (g b) does, and a is not known to be
; equal to b), so matching (f x y) with (f a b) does not produce an
; instantiation.
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U U) U)
(declare-fun g (U) U)
(declare-fun h (U) U)
(declare-fun a () U)
(declare-fun b () U)
(assert (forall ((x U) (y U)) (! (= (f x y) (h y)) :pattern ((g x) (f x y)))))
(assert (= (g b) b))
(assert (not (= (f a b) (h b))))
(check-sat)
