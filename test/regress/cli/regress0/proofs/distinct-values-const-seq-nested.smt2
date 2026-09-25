; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun x () (Seq (Seq Int)))
(declare-fun z () (Seq Int))
(declare-fun b () Bool)
(assert (= x (ite b (seq.unit (seq.unit 1)) (seq.++ (seq.unit (seq.unit 2)) (seq.unit (seq.unit 3))))))
(assert (= x (seq.++ (seq.unit z) (seq.unit z))))
(check-sat)
