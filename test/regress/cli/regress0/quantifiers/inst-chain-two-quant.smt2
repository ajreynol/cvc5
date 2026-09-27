; REQUIRES: unrestricted-mode
; COMMAND-LINE: --inst-chain --inst-chain-depth=4
; COMMAND-LINE: --inst-chain --inst-chain-depth=4 --user-pat=strict
; EXPECT: unsat
; Two quantified formulas whose triggers alternate along the chain: the body of
; each creates the ground term matching the other's pattern.
(set-logic UF)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun g (U) U)
(declare-fun h (U) U)
(declare-fun P (U) Bool)
(declare-fun Q (U) Bool)
(assert (forall ((x U)) (! (=> (P x) (Q (g x))) :pattern ((P x)))))
(assert (forall ((y U)) (! (=> (Q y) (P (h y))) :pattern ((Q y)))))
(assert (P a))
(assert (not (Q (g (h (g (h (g a)))))))) 
(check-sat)
