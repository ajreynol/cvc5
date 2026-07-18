; Tests the :exec RARE rule arith-sine-double, applied by the last-effort
; executable rewrite trie (a "direct", no-:list-variable pattern). The
; double-angle identity sin(2x) = 2*sin(x)*cos(x) is not applied by the
; hand-written rewriter, so (sin (* 2 x)) survives until the exec pass rewrites
; it. As the identity holds, its negation is unsatisfiable, and the exec rewrite
; lets the rewriter close this without any nonlinear reasoning. We check proofs
; to exercise the THEORY_REWRITE step produced for the exec rewrite.
; COMMAND-LINE: --check-proofs
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () Real)
(assert (not (= (sin (* 2.0 x)) (* 2.0 (sin x) (cos x)))))
(check-sat)
