; The base constructor (leaf) is declared last and no tester for a occurs in
; the input, so the splitting lemma for a is the only thing that decides its
; constructor. --dt-split-order=base-first puts is-leaf first, which ends the
; constructor recursion; the default and base-last put is-node first, which
; requires expanding a into node(l a, r a) and splitting again.
; The ordering modes are refused with proofs and unsat cores, since the
; conclusion of the DT_SPLIT proof rule is the lemma in declaration order.
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
; DISABLE-TESTER: alethe
; DISABLE-TESTER: cpc
; DISABLE-TESTER: cpc-logos
; COMMAND-LINE: --dt-split-order=base-first
; COMMAND-LINE: --dt-split-order=base-last
; COMMAND-LINE: --dt-split-order=base-first --dt-split-prefer-phase
; COMMAND-LINE: --dt-split-order=base-first --decision=justification
; EXPECT: sat
(set-logic UFDTLIA)
(declare-datatype T ((node (l T) (r T)) (pair (p Int) (q Int)) (leaf)))
(declare-fun a () T)
(assert (or (= (p a) 1) (= (p a) 2)))
(assert (or (= (l a) leaf) ((_ is pair) (l a))))
(check-sat)
