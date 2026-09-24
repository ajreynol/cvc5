; EXPECT: unsat
; x = y ++ z with y, z in (ab)*, the approximation of x is included in
; (ab)*, which conflicts with (not (str.in_re x (ab)*)). Times out.
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= x (str.++ y z)))
(assert (str.in_re y (re.* (str.to_re "ab"))))
(assert (str.in_re z (re.* (str.to_re "ab"))))
(assert (not (str.in_re x (re.* (str.to_re "ab")))))
(check-sat)
