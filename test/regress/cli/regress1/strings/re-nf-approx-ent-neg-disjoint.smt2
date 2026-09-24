; EXPECT: sat
; x = y ++ z with y in a+, the approximation a+ ++ re.all of x is
; disjoint from b*, which entails (not (str.in_re x b*)).
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= x (str.++ y z)))
(assert (str.in_re y (re.+ (str.to_re "a"))))
(assert (not (str.in_re x (re.* (str.to_re "b")))))
(assert (> (str.len z) 10))
(check-sat)
