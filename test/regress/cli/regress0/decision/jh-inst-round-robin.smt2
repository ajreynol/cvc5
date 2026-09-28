; COMMAND-LINE: --no-cbqi --e-matching --user-pat=use --sat-solver=cadical --jh-inst-round-robin
; COMMAND-LINE: --no-cbqi --e-matching --user-pat=use --sat-solver=cadical --no-jh-inst-round-robin
; COMMAND-LINE: --no-cbqi --e-matching --user-pat=use --sat-solver=minisat --jh-inst-round-robin --jh-rlv-order
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; Two quantifiers each produce a batch of instance lemmas. Exercise their
; interleaving, a conflict, repeated solving, and removal of a new group on pop.
(set-logic UF)
(set-option :incremental true)
(set-option :finite-model-find true)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun p (U) Bool)
(declare-fun r (U) Bool)
(declare-fun s (U) Bool)
(declare-fun t (U) Bool)
(declare-fun u (U) Bool)
(declare-fun v (U) Bool)
(assert (distinct a b))
(assert (forall ((x U)) (! (or (p x) (r x)) :pattern ((u x)))))
(assert (forall ((x U)) (! (or (s x) (t x)) :pattern ((v x)))))
(assert (u a))
(assert (u b))
(assert (v a))
(assert (v b))
(check-sat)

(push 1)
(assert (not (or (p a) (r a))))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(declare-fun c () U)
(declare-fun w (U) Bool)
(declare-fun z (U) Bool)
(assert (distinct a b c))
(assert (u c))
(assert (v c))
(assert (forall ((x U)) (! (or (w x) (z x)) :pattern ((u x)))))
(check-sat)
(pop 1)
(check-sat)
