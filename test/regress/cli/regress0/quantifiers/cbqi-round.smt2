; COMMAND-LINE: --cbqi --cbqi-round-budget=-1 --user-pat=strict
; COMMAND-LINE: --cbqi --cbqi-round-budget=0 --user-pat=strict
; COMMAND-LINE: --cbqi --cbqi-round-share --user-pat=strict
; COMMAND-LINE: --cbqi --cbqi-round-budget=2 --cbqi-round-share --user-pat=strict
; COMMAND-LINE: --cbqi --cbqi-round-budget=0 --cbqi-round-share
; EXPECT: unsat
; Two kinds of quantifier under --user-pat=strict: the patterned one is owned
; by the instantiation engine and carries the refutation, one E-matching round
; per link of the chain; the unpatterned one is the only kind conflict-based
; instantiation is allowed to touch. The four cbqi-round modes must agree.
(set-logic UFLIA)
(declare-fun p (Int) Bool)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (! (=> (p x) (p (+ x 1))) :pattern ((p x)))))
(assert (p 0))
(assert (not (p 8)))
(assert (forall ((y Int)) (=> (P y) (Q y))))
(assert (P 101))
(assert (P 102))
(check-sat)
