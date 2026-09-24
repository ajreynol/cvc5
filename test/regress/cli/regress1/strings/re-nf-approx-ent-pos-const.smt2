; EXPECT: sat
; x = y ++ "c" ++ z, the approximation [ab]* ++ "c" ++ [ab]* of x is
; included in [a-c]*, which entails (str.in_re x [a-c]*).
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= x (str.++ y "c" z)))
(assert (str.in_re y (re.* (re.range "a" "b"))))
(assert (str.in_re z (re.* (re.range "a" "b"))))
(assert (str.in_re x (re.* (re.range "a" "c"))))
(assert (> (str.len y) 10))
(assert (> (str.len z) 10))
(check-sat)
