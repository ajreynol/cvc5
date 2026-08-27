; note: cpc reference checking not supported, declare-codatatypes cannot appear in an ethos reference file
; DISABLE-TESTER: cpc
; REQUIRES: unrestricted-mode
(set-logic QF_ALL)
(set-info :status unsat)

(declare-codatatypes ((Stream 0)) (((S (s Stream)))))

(declare-fun x () Stream)
(declare-fun y () Stream)

(assert (not (= x y)))

(check-sat)
