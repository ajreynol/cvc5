; COMMAND-LINE: --dt-share-sel
; EXPECT: sat
(set-logic ALL)
(declare-datatypes ((D 0)) (((A (x Int) (y Int)) (B (z Int)))))
(declare-datatypes ((E 1)) ((par (X) ((L (lv X)) (R (rv X) (rw Int))))))
; selectors applied to terms built by other constructors are unconstrained
(assert (= (x (B 5)) 6))
(declare-const v D)
(assert ((_ is B) v))
(assert (not (= (x v) (z v))))
(declare-const w (E Int))
(assert ((_ is R) w))
(assert (not (= (lv w) (rv w))))
(check-sat)
