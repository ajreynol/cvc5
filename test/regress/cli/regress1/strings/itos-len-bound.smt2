; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun z () Int)
; unsat since (str.from_int z) has at most max(z,1) characters, hence z is
; never a valid start position of the substring below
(assert (not (= (str.substr (str.from_int z) z z) "")))
(check-sat)
