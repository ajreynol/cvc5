; EXPECT: sat
; x = y ++ z with y, z in (ab)*, the approximation (ab)* ++ (ab)* of x is
; included in (ab)*, which entails (str.in_re x (ab)*). Notice that unlike
; for re-nf-approx-ent-pos-concat, the membership of x cannot be rewritten to
; memberships of y and z.
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= x (str.++ y z)))
(assert (str.in_re y (re.* (str.to_re "ab"))))
(assert (str.in_re z (re.* (str.to_re "ab"))))
(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (> (str.len x) 20))
(check-sat)
