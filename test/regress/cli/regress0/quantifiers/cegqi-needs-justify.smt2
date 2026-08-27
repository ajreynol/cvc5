; note: cpc reference checking not supported, numerals in this file are Real-typed by cvc5 but Int-typed by ethos
; DISABLE-TESTER: cpc
(set-logic NRA)
(set-info :status unsat)
(declare-fun c () Real)
(declare-fun t () Real)
(assert (forall ((s Real)) (and (> t 0) (= 0 (* t c)) (or (< s c) (> s 1.0)))))
; previously answered "sat" with --nl-ext=none --nl-rlv=always
(check-sat)
