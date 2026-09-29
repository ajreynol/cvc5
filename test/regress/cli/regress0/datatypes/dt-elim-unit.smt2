; COMMAND-LINE: --dt-elim --incremental
; DISABLE-TESTER: model
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(declare-datatype Unit ((unit)))
(declare-datatype Pair ((pair (first Unit) (second Int))))
(declare-const u Unit)
(declare-fun f (Unit) Int)
(declare-fun g (Int) Unit)
(declare-fun h (Pair) Pair)
(assert (= (f u) 8))
(assert (= (second (h (pair (g 0) 3))) 4))
(check-sat)
(push 1)
(assert (distinct (f (g 12)) 8))
(check-sat)
(pop 1)
(assert (exists ((v Unit)) (distinct (f v) 8)))
(check-sat)
