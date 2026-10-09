; COMMAND-LINE: --eager-inst --no-e-matching --no-cegqi --no-enum-inst --no-cbqi --no-mbqi --simplification=none
; DISABLE-TESTER: unsat-core
; EXPECT: unsat
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun p (U) Bool)
(declare-fun r (U) Bool)
(declare-fun a () U)
; the four instances are the four 2-literal clauses over p(f a) and r(f a),
; which are unsatisfiable but contain no unit, so a refutation needs a decision
(assert (forall ((x U)) (! (or (p (f x)) (r (f x))) :pattern ((f x)) :qid q1)))
(assert (forall ((x U)) (! (or (not (p (f x))) (not (r (f x)))) :pattern ((f x)) :qid q2)))
(assert (forall ((x U)) (! (or (p (f x)) (not (r (f x)))) :pattern ((f x)) :qid q3)))
(assert (forall ((x U)) (! (or (not (p (f x))) (r (f x))) :pattern ((f x)) :qid q4)))
(assert (not (= (f a) a)))
(check-sat)
