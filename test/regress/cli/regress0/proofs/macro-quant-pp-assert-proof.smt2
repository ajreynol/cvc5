; REQUIRES: no-safe-mode
; COMMAND-LINE: --dump-proofs --proof-granularity=dsl-rewrite --check-proofs --proof-check=eager --no-proof-allow-trust
; SCRUBBER: grep -o 'unsat\|lambda-elim\|macro-quant-macro-def\|trust'
; EXPECT: unsat
; EXPECT: lambda-elim
(set-logic UFLIA)
(set-option :macros-quant true)

(declare-fun P (Int) Bool)

(assert (forall ((x Int)) (P x)))
(assert (not (P 0)))

(check-sat)
