; EXPECT: unsat
; x = y ++ z with y in [a-z]*, z in [0-9]+, the approximation of x is
; disjoint from [a-z]* ++ ".", which conflicts with the membership of x.
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= x (str.++ y z)))
(assert (str.in_re y (re.* (re.range "a" "z"))))
(assert (str.in_re z (re.+ (re.range "0" "9"))))
(assert (str.in_re x (re.++ (re.* (re.range "a" "z")) (str.to_re "."))))
(check-sat)
