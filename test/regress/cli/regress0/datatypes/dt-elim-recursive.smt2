; COMMAND-LINE: --dt-elim --incremental
; DISABLE-TESTER: model
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
(set-logic ALL)
(declare-datatypes ((P 0) (L 0))
  (((wrap (number Int) (rest L)))
   ((nil) (cons (head P)))))
(declare-const x L)
(assert ((_ is cons) x))
(assert (= (number (head x)) 10))
(check-sat)
(push 1)
(assert (= (rest (head x)) x))
(check-sat)
(pop 1)
(assert (= (rest (head x)) nil))
(assert (= x (cons (wrap 10 nil))))
(check-sat)
