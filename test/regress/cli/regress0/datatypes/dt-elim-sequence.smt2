; COMMAND-LINE: --dt-elim
; REQUIRES: no-competition
; EXIT: 1
; EXPECT: (error "dt-elim cannot inline datatype in type (Seq Pair)")
(set-logic ALL)
(declare-datatype Pair ((pair (first Int) (second Bool))))
(declare-const s (Seq Pair))
(assert (= (seq.nth s 0) (pair 0 true)))
(check-sat)
