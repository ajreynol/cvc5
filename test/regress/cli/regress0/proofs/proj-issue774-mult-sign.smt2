; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-fun s () Real)
(declare-fun k () Real)
(assert (and (< s 1) (<= k 1) (< (div 0 1) s) (= 0.0 (+ 1 (* (- k) s k (- (abs (+ 1 (* s s k (- 1))))))))))
(check-sat)
