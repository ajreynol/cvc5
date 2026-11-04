; COMMAND-LINE: --eager-e-matching
; EXPECT: (error "Error in option parsing: --eager-e-matching is not supported in higher-order logic")
; EXIT: 1
; The core has no support for lambdas, whose bound variables would reach its
; E-graph and its instances.
(set-logic HO_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(assert (forall ((g (-> U U))) (= g f)))
(check-sat)
