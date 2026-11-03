; COMMAND-LINE: --z3 --incremental --no-e-matching
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; The forms of instances are cached per user context, so that cvc5's
; preprocessing gives the definitions of their skolems again after a pop.
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun p (Int) Bool)
(declare-fun a () Int)
(assert (forall ((x Int)) (! (= (f x) (ite (p x) (+ x 1) (- x 1))) :pattern ((f x)))))
(push 1)
(assert (p a))
(assert (not (= (f a) (+ a 1))))
(check-sat)
(pop 1)
(push 1)
(assert (not (p a)))
(assert (not (= (f a) (- a 1))))
(check-sat)
(pop 1)
(push 1)
(assert (p a))
(assert (not (= (f a) (+ a 1))))
(check-sat)
(pop 1)
