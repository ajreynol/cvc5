; COMMAND-LINE: --pre-skolem-quant=on
; COMMAND-LINE: --pre-skolem-quant=on --no-pre-skolem-quant-nested
; EXPECT: unsat
(set-logic UFLIA)
(declare-sort U 0)
(declare-fun P (U) Bool)
(declare-fun Q (U U) Bool)
(declare-fun R (Int) Bool)
(declare-fun f (Int) Int)
; the negated quantified formulas are pre-skolemized during preprocessing
(assert (or (not (forall ((x U)) (P x))) (exists ((y U)) (not (forall ((z U)) (Q y z))))))
(assert (forall ((x U)) (P x)))
(assert (or (forall ((x U) (y U)) (Q x y)) (not (R 0))))
; the nested negated quantified formula is pre-skolemized during preprocessing
; if pre-skolem-quant-nested is enabled, and in instances otherwise
(assert (forall ((x Int)) (or (R x) (not (forall ((y Int)) (> (f y) x))))))
(assert (forall ((x Int)) (> (f x) 5)))
(check-sat)
