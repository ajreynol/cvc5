; Tests the :exec RARE rule re-star-star, which replaces the hand-written
; rewrite that used to collapse a nested star (Rewrite::RE_STAR_NESTED_STAR in
; strings/sequences_rewriter.cpp). This is the intended migration path: a
; rewrite implemented by hand is deleted in favour of the RARE rule, which the
; executable rewrite database applies as a last resort.
;
; Since (re.* (re.* r)) and (re.* r) denote the same language, asserting a
; membership in the former and its negation in the latter is unsatisfiable,
; which is closed by the executable rewrite alone.
;
; We check proofs to exercise the THEORY_REWRITE_EXEC step, which is elaborated
; into a DSL_REWRITE step for re-star-star.
; COMMAND-LINE: --check-proofs
; EXPECT: unsat
(set-logic ALL)
(declare-fun s () String)
(declare-fun r () RegLan)
(assert (str.in_re s (re.* (re.* r))))
(assert (not (str.in_re s (re.* r))))
(check-sat)
