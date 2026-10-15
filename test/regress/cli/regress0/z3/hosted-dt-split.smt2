; COMMAND-LINE: --z3
; COMMAND-LINE: --z3 --z3-theory-engine=z3 --z3-preset=z3
; COMMAND-LINE: --z3 --z3-theory-engine=z3
; EXPECT: sat
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; cvc5's prop engine over the ported Z3 theory engine: the case split of the
; datatypes theory on (tl x) reaches cvc5 as a splitting lemma, whose atom
; cvc5's rewriter turns into an equality with nil; the theory side must still
; receive that equality, although it is not relevant there
(set-logic QF_UFDTLIA)
(declare-datatype Lst ((nil) (cons (hd Int) (tl Lst))))
(declare-fun x () Lst)
(assert ((_ is cons) x))
(check-sat)
