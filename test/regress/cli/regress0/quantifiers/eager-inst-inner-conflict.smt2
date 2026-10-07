; COMMAND-LINE: --eager-inst --no-e-matching --no-cegqi --no-enum-inst --no-cbqi --no-mbqi
; DISABLE-TESTER: unsat-core
; EXPECT: unsat
; The conflict needs both instances at once, so it is one that the inner SMT
; solver finds and exports as (or (not q1) (not q2)).
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun p (U) Bool)
(declare-fun a () U)
(assert (forall ((x U)) (! (p (f x)) :pattern ((f x)) :qid q1)))
(assert (forall ((x U)) (! (not (p (f x))) :pattern ((f x)) :qid q2)))
(assert (not (= (f a) a)))
(check-sat)
