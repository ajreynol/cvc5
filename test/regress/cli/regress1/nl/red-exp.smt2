; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
; COMMAND-LINE: --nl-ext=full
; EXPECT: unsat
(set-logic QF_NRA)
(set-info :status unsat)

(declare-fun a () Real)
(declare-fun b () Real)

(assert (or (= a (* b b)) (and (= a 9) (= b 3))))
(assert (not (= (* a a) (* b b b b))))
(check-sat)
