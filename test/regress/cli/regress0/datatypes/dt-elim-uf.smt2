; COMMAND-LINE: --dt-elim --incremental
; DISABLE-TESTER: model
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
(set-logic ALL)
(declare-datatype Pair ((pair (first Int) (second Bool))))
(declare-const x Pair)
(declare-const y Pair)
(declare-fun f (Pair Int) Pair)
(assert (= (first x) 1))
(assert (second x))
(assert (= (first (f x 0)) 2))
(assert (not (second (f x 0))))
(check-sat)
(push 1)
(assert (= (first y) (first x)))
(assert (= (second y) (second x)))
(assert (distinct (f x 0) (f y 0)))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (= (first (f x 0)) 3))
(check-sat)
(pop 1)
(check-sat)
