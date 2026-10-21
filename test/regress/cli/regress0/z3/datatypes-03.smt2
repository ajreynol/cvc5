; COMMAND-LINE: --z3
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: unsat-core
(set-logic UFDTLIA)
(declare-datatype Lst ((nil) (cons (hd Int) (tl Lst))))
(declare-fun f (Lst) Int)
(assert (forall ((l Lst)) (! (= (f (cons 0 l)) 1) :pattern ((f (cons 0 l))))))
(assert (not (= (f (cons 0 nil)) 1)))
(check-sat)
