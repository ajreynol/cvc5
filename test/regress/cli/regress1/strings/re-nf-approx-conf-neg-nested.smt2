; EXPECT: unsat
; x = y ++ y and y = u ++ "a" with u in a*, the approximation of x
; (computed via the normal form of y) is included in a+, which conflicts
; with (not (str.in_re x a+)).
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const u String)
(assert (= x (str.++ y y)))
(assert (= y (str.++ u "a")))
(assert (str.in_re u (re.* (str.to_re "a"))))
(assert (not (str.in_re x (re.+ (str.to_re "a")))))
(check-sat)
