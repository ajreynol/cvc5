; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
(set-option :incremental false)
(set-info :status unsat)
(set-info :category "crafted")
(set-info :difficulty "0")
(set-logic QF_LRA)

(declare-fun x_0 () Real)
(declare-fun x_1 () Real)
(declare-fun b_f () Bool)
(assert (<= x_0 0))
(assert (<= x_1 0))
(assert (not b_f))
(assert (ite b_f b_f (>= (+ x_0 x_1) 1)))
(check-sat)
