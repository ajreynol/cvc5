; REQUIRES: unrestricted-mode
; COMMAND-LINE: --inst-chain --inst-chain-depth=8
; COMMAND-LINE: --inst-chain --inst-chain-depth=8 --inst-chain-limit=2
; COMMAND-LINE: --inst-chain --user-pat=strict
; EXPECT: unsat
; A chain of instantiations in which each link creates the term that fires the
; next. With --inst-chain the whole chain is derived within a single
; instantiation round.
(set-logic UF)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun f (U) U)
(declare-fun P (U) Bool)
(assert (forall ((x U)) (! (=> (P x) (P (f x))) :pattern ((P x)))))
(assert (P a))
(assert (not (P (f (f (f (f (f (f (f (f a)))))))))))
(check-sat)
