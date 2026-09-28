; --dt-split-prefer-phase only sets a SAT phase preference, it does not change
; the splitting lemma, so unlike --dt-split-order it stays compatible with
; proofs and unsat cores. No tester is disabled here on purpose: this test
; exists to keep that compatibility. Coverage of the option on inputs that do
; emit splitting lemmas is in dt-split-order.smt2 and dt-split-order-multi.smt2.
; COMMAND-LINE: --dt-split-prefer-phase
; COMMAND-LINE: --dt-split-prefer-phase --decision=justification
; EXPECT: unsat
(set-logic UFDTLIA)
(declare-datatype T ((node (l T) (r T) (k Int)) (leaf)))
(declare-fun a () T)
(assert (>= (k a) 0))
(assert (=> ((_ is node) a) (< (k a) 0)))
(assert (=> ((_ is leaf) a) (< (k a) 0)))
(check-sat)
