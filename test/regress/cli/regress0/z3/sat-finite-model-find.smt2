; COMMAND-LINE: --z3 --finite-model-find
; EXPECT: sat
; The core claims completeness for no quantified formula, which leaves it to
; the module of cvc5's quantifiers engine that does, here finite model
; finding.
(set-logic UF)
(declare-sort U 0)
(declare-fun P (U) Bool)
(declare-const a U)
(assert (forall ((x U)) (! (P x) :pattern ((P x)))))
(assert (P a))
(check-sat)
