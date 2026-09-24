; EXPECT: unsat
; Same as re-nf-approx-cst-odd with a longer constant, which is slow
; since the constant is split character by character.
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= x (str.++ y z)))
(assert (str.in_re y (re.* (str.to_re "ab"))))
(assert (str.in_re z (re.* (str.to_re "ab"))))
(assert (= x "ababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababa"))
(check-sat)
