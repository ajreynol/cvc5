; EXPECT: unsat
; x = y ++ z with y in b+, the approximation b+ ++ re.all of x is
; disjoint from a*, which conflicts with (str.in_re x a*).
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= x (str.++ y z)))
(assert (str.in_re y (re.+ (str.to_re "b"))))
(assert (str.in_re x (re.* (str.to_re "a"))))
(check-sat)
