; EXPECT: unsat
; x = y ++ z with y, z in (ab)*, neither possible constant value of x is
; in the approximation (ab)* ++ (ab)* of x, which is a conflict. Slow.
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(declare-const b Bool)
(assert (= x (str.++ y z)))
(assert (str.in_re y (re.* (str.to_re "ab"))))
(assert (str.in_re z (re.* (str.to_re "ab"))))
(assert (= x (ite b "ababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababa" "abababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababa")))
(check-sat)
