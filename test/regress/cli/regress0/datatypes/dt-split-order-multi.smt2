; Several datatype terms each needing a constructor split, so that the
; reordering applies more than once.
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
; DISABLE-TESTER: alethe
; DISABLE-TESTER: cpc
; DISABLE-TESTER: cpc-logos
; COMMAND-LINE: --dt-split-order=base-first
; COMMAND-LINE: --dt-split-order=base-last
; COMMAND-LINE: --dt-split-order=base-first --dt-split-prefer-phase --decision=justification
; EXPECT: sat
(set-logic UFDTLIA)
(declare-datatype T ((node (l T) (r T)) (pair (p Int) (q Int)) (leaf)))
(declare-fun a0 () T)
(declare-fun a1 () T)
(declare-fun a2 () T)
(declare-fun a3 () T)
(assert (or (= (p a0) 1) (= (p a0) 2)))
(assert (or (= (l a0) leaf) ((_ is pair) (l a0))))
(assert (or (= (p a1) 1) (= (p a1) 2)))
(assert (or (= (l a1) leaf) ((_ is pair) (l a1))))
(assert (or (= (p a2) 1) (= (p a2) 2)))
(assert (or (= (l a2) leaf) ((_ is pair) (l a2))))
(assert (or (= (p a3) 1) (= (p a3) 2)))
(assert (or (= (l a3) leaf) ((_ is pair) (l a3))))
(assert (= (+ (p a0) (p a1) (p a2) (p a3)) 6))
(check-sat)
