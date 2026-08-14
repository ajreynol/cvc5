; Tests that -o rare-db-exec prints the C++ implementation of the single step
; rewrite given by the :exec RARE rules, which is the contents of
; rewriter/rewrite_db_exec.cpp. We scrub everything but the markers of the
; features the implementation covers:
;   - the matching routine, which is a single traversal for all of the rules,
;   - reading the indices off an indexed operator (bv-extract-not),
;   - searching for the needle of a :list variable sandwich (re-union-all).
; COMMAND-LINE: -o rare-db-exec
; SCRUBBER: grep -oE "RewriteDbExec::getMatches|GenericOp::getIndicesForOperator|mkListArg" | sort -u
; EXPECT: GenericOp::getIndicesForOperator
; EXPECT: mkListArg
; EXPECT: RewriteDbExec::getMatches
(set-logic ALL)
(assert true)
(check-sat)
