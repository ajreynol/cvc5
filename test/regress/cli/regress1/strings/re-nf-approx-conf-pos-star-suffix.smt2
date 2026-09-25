; EXPECT: unsat
; x = y ++ z with z in [0-9]+, the approximation of x ends with a digit, so
; it is disjoint from (ab)* ++ ".", which conflicts with the membership of x.
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= x (str.++ y z)))
(assert (str.in_re y (re.* (str.to_re "ab"))))
(assert (str.in_re z (re.+ (re.range "0" "9"))))
(assert (str.in_re x (re.++ (re.* (str.to_re "ab")) (str.to_re "."))))
(assert (> (str.len z) 3))
(assert (> (str.len y) 3))
(check-sat)
