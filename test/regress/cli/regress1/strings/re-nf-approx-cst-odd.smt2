; EXPECT: unsat
; x = y ++ z with y, z in (ab)*, the constant x is not in the
; approximation (ab)* ++ (ab)* of x, which is a conflict.
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= x (str.++ y z)))
(assert (str.in_re y (re.* (str.to_re "ab"))))
(assert (str.in_re z (re.* (str.to_re "ab"))))
(assert (= x "ababababababababababababababababababababababababababababababa"))
(check-sat)
