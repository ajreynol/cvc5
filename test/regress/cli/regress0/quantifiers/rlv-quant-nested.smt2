; REQUIRES: unrestricted-mode
; COMMAND-LINE: --rlv-quant=full
; EXPECT: unsat
; Instantiating the outer quantified formula produces a lemma one of whose
; literals is the inner quantified formula. The SAT solver assigns that literal
; true, but it is not part of any relevant selection of the input, so
; --rlv-quant=full withholds it from instantiation at full effort and considers
; it again at last call. The answer must not change.
(set-logic UF)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun f (U) U)
(declare-fun P (U) Bool)
(declare-fun R (U) Bool)
(assert (forall ((x U)) (! (or (P (f x)) (forall ((y U)) (! (R y) :pattern ((R y)))))
                           :pattern ((P x)))))
(assert (P a))
(assert (not (P (f (f (f a))))))
(assert (not (R a)))
(check-sat)
