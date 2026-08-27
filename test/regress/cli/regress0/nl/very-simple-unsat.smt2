; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
; COMMAND-LINE: --nl-ext=full
; EXPECT: unsat
(set-logic QF_NRA)
(set-info :source |
Harald Roman Zankl <Harald.Zankl@uibk.ac.at>

|)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun a () Real)
(assert (= (* a a) (- 2)))
(check-sat)
(exit)

