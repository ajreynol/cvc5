; REQUIRES: statistics
; COMMAND-LINE: --simplification=none --arith-prop-clauses=0 --stats
; ERROR-SCRUBBER: grep -o 'theory::arith::inferencesPropagation = { ARITH_PROP'
; EXPECT: sat
; EXPECT-ERROR: theory::arith::inferencesPropagation = { ARITH_PROP
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun b () Bool)
(assert (>= x 1))
(assert (>= y 1))
(assert (or (>= (+ x y) 1) b))
(check-sat)
