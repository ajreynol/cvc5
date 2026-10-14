; COMMAND-LINE: --produce-unsat-cores --check-proofs --check-unsat-cores
; EXPECT: unsat
; EXPECT: (
; EXPECT: singleton
; EXPECT: )
(set-logic UF)
(declare-sort-parameter A)
(assert (! (forall ((x A) (y A)) (= x y)) :named singleton))
(check-sat)
(get-unsat-core)
