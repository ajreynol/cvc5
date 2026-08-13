; Tests a *conditional* :exec RARE rule (arith-sine-quad) applied by the
; executable rewrite trie. Its condition is verified by rewriting it to true
; before the rule fires, which is done by queuing it as another rewrite job;
; note the condition of this rule holds only by applying the :exec rule
; arith-sine-double. As the identity sin(4x) = 2*sin(2x)*cos(2x) holds, its
; negation is unsatisfiable, closed via the exec rewrite. We check proofs to
; exercise the REWRITE_EXEC step produced for the rewrite, which is elaborated
; into a DSL_REWRITE step for arith-sine-quad whose premise is the DSL_REWRITE
; step for arith-sine-double that discharges its condition.
; COMMAND-LINE: --check-proofs
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () Real)
(assert (not (= (sin (* 4.0 x)) (* 2.0 (sin (* 2.0 x)) (cos (* 2.0 x))))))
(check-sat)
