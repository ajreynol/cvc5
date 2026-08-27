; note: cpc reference checking not supported, define-funs-rec cannot appear in an ethos reference file
; DISABLE-TESTER: cpc
(set-logic ALL)
(set-info :status unsat)

(define-funs-rec (
(f () Int)
(pred ((y Int)) Bool)) (
0
(ite (< y 0) false (ite (= y 0) true (pred (- y 2))))
))

(assert (pred 5))
(check-sat)
