; COMMAND-LINE: --eager-inst
; COMMAND-LINE: --eager-inst --eager-inst-output=lemma --no-e-matching
; EXPECT: unsat
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun h (U) U)
(declare-fun p (U) Bool)
(declare-fun a () U)
(declare-fun d () U)
(assert (forall ((x U)) (! (p (f (h x))) :pattern ((f (h x))))))
(assert (not (p (f d))))
(assert (= (h a) d))
(check-sat)
