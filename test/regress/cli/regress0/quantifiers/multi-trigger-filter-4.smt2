; COMMAND-LINE: --no-cbqi --no-enum-inst
; COMMAND-LINE: --no-cbqi --no-enum-inst --no-multi-trigger-filter
; A multi-trigger with a non-simple base term (f x (h y)) and a filter term
; (g x 0) containing a ground argument.
(set-logic UFLIA)
(set-info :status unsat)
(declare-fun f (Int Int) Int)
(declare-fun g (Int Int) Int)
(declare-fun h (Int) Int)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(assert (forall ((x Int) (y Int))
  (! (> (f x (h y)) (+ x y)) :pattern ((g x 0) (f x (h y))))))
(assert (= (g b (- c c)) 5))
(assert (= a b))
(assert (<= (f a (h c)) (+ a c)))
(check-sat)
