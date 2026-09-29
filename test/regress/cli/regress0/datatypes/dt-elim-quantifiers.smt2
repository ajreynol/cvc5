; COMMAND-LINE: --dt-elim
; EXPECT: unsat
(set-logic ALL)
(declare-datatype Pair ((pair (first Int) (second Bool))))
(declare-fun f (Pair) Pair)
(declare-const a Pair)
(assert (forall ((x Pair)) (! (= (f x) x) :pattern ((f x)))))
(assert (distinct (f a) a))
(check-sat)
