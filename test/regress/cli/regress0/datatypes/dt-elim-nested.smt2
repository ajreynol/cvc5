; COMMAND-LINE: --dt-elim --incremental
; DISABLE-TESTER: model
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
(set-logic ALL)
(declare-datatype Pair ((pair (first Int) (second Bool))))
(declare-datatype Box (par (T) ((box (value T)))))
(declare-datatype Choice ((empty) (some (payload (Box Pair)) (tag Int))))
(declare-const x Choice)
(declare-const b Bool)
(declare-fun f ((Box Pair)) (Box Pair))
(assert ((_ is some) x))
(assert (= (first (value (payload x))) 7))
(assert (second (value (payload x))))
(assert (= (tag x) 4))
(assert (= (f (payload x)) (ite b (box (pair 7 true)) (box (pair 8 false)))))
(check-sat)
(push 1)
(assert (distinct ((_ update payload) x (box (pair 9 false)))
                  (some (box (pair 9 false)) 4)))
(check-sat)
(pop 1)
; Selectors on the wrong constructor remain unconstrained.
(assert (= (first (value (payload empty))) 13))
(assert (not (second (value (payload empty)))))
(check-sat)
