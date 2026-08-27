; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
; REQUIRES: unrestricted-mode
; DISABLE-TESTER: alethe
; COMMAND-LINE: --cegqi-inf-int --sat-solver=minisat
; EXPECT: unsat
(set-logic ALL)
(declare-fun a () Real)
(assert
  (forall ((v Int) (r Int))
    (distinct true (>= r (* v (- 1 a) (/ 1 2))))))
(check-sat)
