; COMMAND-LINE: --eager-inst --no-e-matching --no-cegqi --no-enum-inst --no-cbqi --no-mbqi --simplification=none
; DISABLE-TESTER: unsat-core
; EXPECT: unsat
; The conflict needs two instances, an equality and a disequality of the outer
; context, and congruence; the inner SMT solver's proof forest gives the
; explanation that all four are needed.
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun g (U) U)
(declare-fun c1 () U)
(declare-fun c2 () U)
(declare-fun a () U)
(assert (forall ((x U)) (! (= (f x) c1) :pattern ((f x)) :qid q1)))
(assert (forall ((x U)) (! (= (g x) c2) :pattern ((g x)) :qid q2)))
(assert (not (= c1 c2)))
(assert (= (f a) (g a)))
(check-sat)
