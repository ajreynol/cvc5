; note: cpc reference checking not supported, define-fun-rec cannot appear in an ethos reference file
; DISABLE-TESTER: cpc
; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(define-fun-rec five () Int 5)
(assert (= five 6))
(check-sat)
