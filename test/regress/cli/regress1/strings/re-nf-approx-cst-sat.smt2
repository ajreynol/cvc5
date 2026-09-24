; EXPECT: sat
; x = y ++ z with y, z in (ab)*, the constant x is in the approximation
; (ab)* ++ (ab)* of x, so no conflict is found.
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= x (str.++ y z)))
(assert (str.in_re y (re.* (str.to_re "ab"))))
(assert (str.in_re z (re.* (str.to_re "ab"))))
(assert (> (str.len y) 50))
(assert (> (str.len z) 50))
(assert (= x "ababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababab"))
(check-sat)
