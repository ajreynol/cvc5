; note: cpc reference checking not supported, define-fun-rec cannot appear in an ethos reference file
; DISABLE-TESTER: cpc
(set-logic UFLIA)
(set-info :status unsat)
(define-fun-rec sumr ((x Int)) Int 
    (+ x (ite (> x 0) (sumr (- x 1)) 0)))
(assert (= (sumr 2) 2))
(check-sat)
