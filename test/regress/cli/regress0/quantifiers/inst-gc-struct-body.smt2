; An instantiation body with Boolean structure. Under --inst-gc=assert only
; the clause that asserts the instance is removable and the Tseitin
; definitions of the body are kept; under --inst-gc=body the definitions are
; removable too.
; Either way the SAT solver may discard a clause a proof or an unsat core
; depends on, and option parsing refuses those combinations, so those testers
; cannot run here.
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
; DISABLE-TESTER: alethe
; DISABLE-TESTER: cpc
; DISABLE-TESTER: cpc-logos
; COMMAND-LINE: --inst-gc=assert --sat-solver=cadical
; COMMAND-LINE: --inst-gc=assert --sat-solver=minisat
; COMMAND-LINE: --inst-gc=body --sat-solver=cadical
; COMMAND-LINE: --inst-gc=body --sat-solver=minisat
; EXPECT: unsat
(set-logic UF)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun a () U)
(declare-fun p (U) Bool)
(declare-fun q (U) Bool)
(declare-fun r (U) Bool)
(declare-fun s (U) Bool)
(assert (forall ((x U)) (! (or (and (p x) (q x)) (and (r x) (s x))) :pattern ((f x)))))
(assert (= (f a) a))
(assert (not (p a)))
(assert (not (r a)))
(check-sat)
