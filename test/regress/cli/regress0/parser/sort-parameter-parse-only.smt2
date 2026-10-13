; COMMAND-LINE: --parse-only --strict-parsing
; EXIT: 0
(set-logic ALL)
(declare-sort-parameter A)
(declare-sort-parameter B)
(declare-fun f (A) A)
(declare-fun is-const ((Array A B)) Bool)
(assert (forall ((x A)) (= (f x) x)))
(assert (forall ((a (Array A B)))
  (= (is-const a)
     (forall ((i A) (j A)) (= (select a i) (select a j))))))
(check-sat)
