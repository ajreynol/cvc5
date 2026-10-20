; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () Int)
(assert (> x 0))
(check-sat-assuming ((< x 0)))
(check-sat-assuming ((< x (- 1))))
