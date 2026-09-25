; EXPECT: sat
; x = y ++ z with y in (ab)+, the approximation of x starts with "a" and
; is non-empty, so it is disjoint from (ba)*, which entails
; (not (str.in_re x (ba)*)).
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= x (str.++ y z)))
(assert (str.in_re y (re.+ (str.to_re "ab"))))
(assert (not (str.in_re x (re.* (str.to_re "ba")))))
(assert (> (str.len z) 10))
(assert (> (str.len y) 3))
(assert (str.in_re z (re.* (str.to_re "c"))))
(check-sat)
