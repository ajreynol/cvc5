; EXPECT: sat
; Same as re-nf-approx-ent-pos-concat with a larger length bound;
; times out due to repeated unfolding of (str.in_re x a*).
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= x (str.++ y z)))
(assert (str.in_re y (re.* (str.to_re "a"))))
(assert (str.in_re z (re.* (str.to_re "a"))))
(assert (str.in_re x (re.* (str.to_re "a"))))
(assert (> (str.len x) 200))
(check-sat)
