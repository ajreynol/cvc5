; Tests that -o rare-db-exec prints the C++ implementation of the single step
; rewrite given by the :exec RARE rules, which is the contents of
; rewriter/rewrite_db_exec.cpp. We scrub everything but the signature of the
; matching routine and the rule it dispatches to.
; COMMAND-LINE: -o rare-db-exec
; SCRUBBER: grep -oE "RewriteDbExec::getMatches|ProofRewriteRule::RE_STAR_STAR" | sort -u
; EXPECT: ProofRewriteRule::RE_STAR_STAR
; EXPECT: RewriteDbExec::getMatches
(set-logic ALL)
(assert true)
(check-sat)
