; REQUIRES: no-safe-mode
; DISABLE-TESTER: alethe
; COMMAND-LINE: --macros-quant --macros-quant-mode=ground --dump-proofs --proof-granularity=dsl-rewrite --check-proofs --proof-check=eager --no-proof-allow-trust
; SCRUBBER: grep -o unsat
; EXPECT: unsat
(set-logic UFLRA)
(declare-fun f (Real Real) Real)
; Solving requires scaling, and the arguments differ from the binder order.
(assert (forall ((x Real) (y Real))
  (! (= (+ (* 3 (f y x)) x) y) :pattern ((f y x)))))
(assert (not (= (f 6 3) 1)))
(check-sat)
