; EXPECT: unsat
; w = x ++ x, x = y ++ z with y in a*, z in b*, the constant w is not in
; the approximation (a* ++ b*) ++ (a* ++ b*) of w, which is a conflict.
(set-logic QF_SLIA)
(declare-const w String)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= w (str.++ x x)))
(assert (= x (str.++ y z)))
(assert (str.in_re y (re.* (str.to_re "a"))))
(assert (str.in_re z (re.* (str.to_re "b"))))
(assert (= w "aaaaaaaaaabbbbbbbbbbbbaaaaaaaaaa"))
(check-sat)
