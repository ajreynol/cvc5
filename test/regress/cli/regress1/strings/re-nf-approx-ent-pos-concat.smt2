; EXPECT: sat
; x = y ++ z with y, z in a*, so the approximation a* ++ a* of x
; is included in a*, which entails (str.in_re x a*).
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= x (str.++ y z)))
(assert (str.in_re y (re.* (str.to_re "a"))))
(assert (str.in_re z (re.* (str.to_re "a"))))
(assert (str.in_re x (re.* (str.to_re "a"))))
(assert (> (str.len x) 20))
(check-sat)
