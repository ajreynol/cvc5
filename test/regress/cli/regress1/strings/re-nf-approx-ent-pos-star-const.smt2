; EXPECT: sat
; x = y ++ "c" ++ z with y, z in (ab)*, the approximation of x is included
; in (ab | c)*, which entails the membership of x.
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= x (str.++ y "c" z)))
(assert (str.in_re y (re.* (str.to_re "ab"))))
(assert (str.in_re z (re.* (str.to_re "ab"))))
(assert (str.in_re x (re.* (re.union (str.to_re "ab") (str.to_re "c")))))
(assert (> (str.len y) 10))
(assert (> (str.len z) 10))
(check-sat)
