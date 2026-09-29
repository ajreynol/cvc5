; COMMAND-LINE: --dt-elim
; REQUIRES: no-competition
; EXIT: 1
; EXPECT: (error "dt-elim cannot inline datatype in type (Array Int Pair)")
(set-logic ALL)
(declare-datatype Pair ((pair (first Int) (second Bool))))
(declare-const a (Array Int Pair))
(assert (= (first (select a 0)) 1))
(check-sat)
