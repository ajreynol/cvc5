; REQUIRES: no-safe-mode
; DISABLE-TESTER: alethe
; COMMAND-LINE: --macros-quant --macros-quant-mode=all --dump-proofs --proof-granularity=dsl-rewrite --check-proofs --proof-check=eager --no-proof-allow-trust
; SCRUBBER: grep -o unsat
; EXPECT: unsat
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(declare-fun Q (Int Int) Bool)
(assert (forall ((x Int)) (= (P x) (forall ((y Int)) (Q x y)))))
(assert (P 0))
(assert (not (Q 0 1)))
(check-sat)
