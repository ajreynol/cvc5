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
(declare-fun e () Real)

(assert (= (* a b c d) 0))

(assert (not (= (* a b c d e) 0)))

(check-sat)
