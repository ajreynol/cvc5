; SCRUBBER: grep -o "Reasoning with global sort parameters is not supported"
; EXPECT: Reasoning with global sort parameters is not supported
; EXIT: 1
; Detect parameters nested in compound sorts and polymorphic function ranks.
(set-logic ALL)
(declare-sort-parameter A)
(declare-sort-parameter B)
(declare-const a (Array A B))
(declare-fun p ((Array A B)) Bool)
(assert (p a))
(check-sat)
