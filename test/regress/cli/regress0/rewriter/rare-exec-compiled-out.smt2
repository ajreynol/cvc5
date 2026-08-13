; Tests that -o rare-db-exec prints the compiled C++ implementation of the
; single step rewrite given by the :exec RARE rules. We scrub everything but
; the signature of the matching routine, which is the compiled counterpart of
; a traversal of the executable rewrite trie.
; COMMAND-LINE: -o rare-db-exec
; SCRUBBER: grep -E "RewriteDbExecCompiled::(getMatches|getResult)" | head -2
; EXPECT: void RewriteDbExecCompiled::getMatches(
; EXPECT: Node RewriteDbExecCompiled::getResult(
(set-logic ALL)
(assert true)
(check-sat)
