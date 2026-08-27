; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
; EXPECT: unsat
(set-logic QF_UFNRA)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun f (Real) Real)
(assert (= (* a a) 2))
(assert (> a 0))
(assert (= (* b b b b) 4))
(assert (< b 0))
(assert (not (= (f (* a a)) (f (* b b)))))
(check-sat)
