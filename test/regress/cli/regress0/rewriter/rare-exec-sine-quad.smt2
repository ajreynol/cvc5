; Tests a *conditional* :exec RARE rule (arith-sine-quad, with the trivially
; true condition (= x x)) applied by the executable rewrite trie. The condition
; is verified by rewriting it to true before the rule fires. As the identity
; sin(4x) = 2*sin(2x)*cos(2x) holds, its negation is unsatisfiable, closed via
; the exec rewrite. We check proofs to exercise the THEORY_REWRITE step for the
; rewrite together with the TRUST_THEORY_REWRITE premise for the condition.
; COMMAND-LINE: --check-proofs
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () Real)
(assert (not (= (sin (* 4.0 x)) (* 2.0 (sin (* 2.0 x)) (cos (* 2.0 x))))))
(check-sat)
