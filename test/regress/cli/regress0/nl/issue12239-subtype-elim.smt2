; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (or (< y 0) (< y 0)))
(assert (=> (>= (to_real 0) (* x y)) (>= (to_real 0) (* x y))))
(assert (< (* x x) (* x (to_real (to_int (- x))))))
(check-sat)
