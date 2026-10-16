; COMMAND-LINE: --z3
; COMMAND-LINE: --z3 --z3-slots=quantifiers
; COMMAND-LINE: --z3 --z3-slots=quantifiers --no-z3-shadow-plugins
; COMMAND-LINE: --z3 --z3-prop-engine=z3 --z3-preset=z3
; EXPECT: sat
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
(set-logic QF_UFDTLIA)
(declare-datatype Lst ((nil) (cons (hd Int) (tl Lst))))
(declare-fun x () Lst)
(assert ((_ is cons) x))
(check-sat)
