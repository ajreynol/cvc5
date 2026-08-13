; Tests that -o rare-db-exec prints the compiled C++ implementation of the
; single step rewrite given by the :exec RARE rules. We scrub everything but
; the signature of the matching routine, which is the compiled counterpart of
; a traversal of the executable rewrite trie, and the rule it dispatches to.
; COMMAND-LINE: -o rare-db-exec
; SCRUBBER: grep -oE "RewriteDbExecCompiled::getMatches|ProofRewriteRule::RE_STAR_STAR" | sort -u
; EXPECT: ProofRewriteRule::RE_STAR_STAR
; EXPECT: RewriteDbExecCompiled::getMatches
(set-logic ALL)
(assert true)
(check-sat)
