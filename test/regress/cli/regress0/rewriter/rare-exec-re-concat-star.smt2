; Tests the :exec RARE rule re-concat-star-dup, applied by the last-effort
; executable rewrite trie. This is a (f t1 s t2) needle pattern: the trie tries
; each child of the re.++ as the needle (re.* r), binding the list variables to
; the surrounding children. Here it matches (re.* (str.to_re "b")) inside
; (re.++ (str.to_re "a") (re.* (str.to_re "b")) (str.to_re "c")). Membership in
; a (b*) c is satisfiable, e.g. by "ac".
; EXPECT: sat
(set-logic ALL)
(declare-fun s () String)
(assert (str.in_re s (re.++ (str.to_re "a") (re.* (str.to_re "b")) (str.to_re "c"))))
(check-sat)
