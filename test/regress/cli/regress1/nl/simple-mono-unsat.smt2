; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
; COMMAND-LINE: --nl-ext=full
; EXPECT: unsat
(set-logic QF_NRA)
(set-info :status unsat)

(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(declare-fun d () Real)

(assert (or (= a 4) (= a 3)))

(assert (> b 0))
(assert (> c 0))

(assert (< (* a b c d d) 0))

(check-sat)
