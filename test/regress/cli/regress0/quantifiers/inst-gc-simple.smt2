; --inst-gc lets the SAT solver discard clauses of an instantiation, which a
; proof or an unsat core may depend on. Option parsing refuses those
; combinations, so those testers cannot run here.
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
; DISABLE-TESTER: alethe
; DISABLE-TESTER: cpc
; DISABLE-TESTER: cpc-logos
; COMMAND-LINE: --inst-gc=assert --sat-solver=cadical
; COMMAND-LINE: --inst-gc=assert --sat-solver=minisat
; COMMAND-LINE: --inst-gc=assert --user-pat=strict --no-cbqi
; COMMAND-LINE: --inst-gc=body --sat-solver=cadical
; COMMAND-LINE: --inst-gc=body --sat-solver=minisat
; EXPECT: unsat
(set-logic UFLIA)
(set-info :status unsat)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun p (Int) Bool)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (forall ((x Int)) (! (=> (p x) (> (f x) (g x))) :pattern ((f x)))))
(assert (forall ((x Int)) (! (=> (> (f x) (g x)) (p (+ x 1))) :pattern ((g x)))))
(assert (p a))
(assert (= b (+ a 1)))
(assert (not (> (f b) (g b))))
(assert (> (f a) 0))
(assert (> (g a) 0))
(check-sat)
