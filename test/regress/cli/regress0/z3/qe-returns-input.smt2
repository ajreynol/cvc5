; COMMAND-LINE: --z3
; EXPECT: (exists ((x Int)) (and (>= x 1) (= y (* 2 x))))
; The ported core eliminates no quantifiers: the query of get-qe is not
; refuted, so the (preprocessed) input is returned, as when cvc5's own
; quantifier elimination fails.
(set-logic LIA)
(declare-fun y () Int)
(get-qe (exists ((x Int)) (and (> x 0) (= y (* 2 x)))))
