; REQUIRES: statistics
; COMMAND-LINE: --simplification=none --ee-mode=distributed --stats
; ERROR-SCRUBBER: grep -o 'theory::uf::inferencesPropagation = { EQ_ENGINE'
; EXPECT: sat
; EXPECT-ERROR: theory::uf::inferencesPropagation = { EQ_ENGINE
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (U) U)
(declare-fun p (U) Bool)
(assert (= a b))
(assert (or (p (f a)) (p (f b))))
(check-sat)
