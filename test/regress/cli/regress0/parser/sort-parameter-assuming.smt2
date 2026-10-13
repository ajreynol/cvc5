; SCRUBBER: grep -o "Reasoning with global sort parameters is not supported"
; EXPECT: Reasoning with global sort parameters is not supported
; EXIT: 1
; Negation does not negate the implicit universal quantifier over sorts.
; This assumption says that EVERY sort has at least two elements.
(set-logic UF)
(declare-sort-parameter A)
(check-sat-assuming ((not (forall ((x A) (y A)) (= x y)))))
