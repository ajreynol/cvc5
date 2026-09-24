; REQUIRES: no-safe-mode
; DISABLE-TESTER: alethe
; COMMAND-LINE: --macros-quant --dump-proofs --proof-granularity=dsl-rewrite --check-proofs --proof-check=eager --no-proof-allow-trust
; SCRUBBER: grep -o unsat
; EXPECT: unsat
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (= (not (P x)) (Q x))))
(assert (= (P 0) (Q 0)))
(check-sat)
