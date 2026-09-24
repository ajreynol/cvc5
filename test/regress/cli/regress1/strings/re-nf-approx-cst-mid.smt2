; EXPECT: unsat
; x = y ++ "c" ++ z with y, z in a*, the constant x is not in the
; approximation a* ++ "c" ++ a* of x, which is a conflict.
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= x (str.++ y "c" z)))
(assert (str.in_re y (re.* (str.to_re "a"))))
(assert (str.in_re z (re.* (str.to_re "a"))))
(assert (= x "aaaaaaaaaaaaaaaaaaaacaaaaaaaaaaaaaaaaaaaabaaaaaaaaaa"))
(check-sat)
