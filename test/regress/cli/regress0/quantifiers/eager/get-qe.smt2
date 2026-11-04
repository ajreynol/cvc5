; COMMAND-LINE: --eager-e-matching
; EXPECT: (let ((_let_1 (div_total y 2))) (and (>= _let_1 1) (= y (* 2 _let_1))))
; The ported core eliminates no quantifiers and claims completeness for none
; of them, so cvc5's counterexample-guided instantiation eliminates it, as
; without --eager-e-matching.
(set-logic LIA)
(declare-fun y () Int)
(get-qe (exists ((x Int)) (and (> x 0) (= y (* 2 x)))))
