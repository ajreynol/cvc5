; COMMAND-LINE: --z3
; EXPECT: unsat
; DISABLE-TESTER: model
(set-logic QF_UFDTLIA)
(declare-datatype Lst ((nil) (cons (hd Int) (tl Lst))))
(declare-fun x () Lst)
(assert (not ((_ is nil) x)))
(assert (not ((_ is cons) x)))
(check-sat)
