; COMMAND-LINE: --dt-elim
; REQUIRES: no-competition
; EXIT: 1
; EXPECT: (error "dt-elim cannot inline datatype in type (Set Pair)")
(set-logic ALL)
(declare-datatype Pair ((pair (first Int) (second Bool))))
(declare-const s (Set Pair))
(assert (set.member (pair 0 true) s))
(check-sat)
