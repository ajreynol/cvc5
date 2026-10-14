; COMMAND-LINE: --term-db-mode=relevance --decision=internal --simplification=none --no-cbqi
; EXPECT: unknown
; The trigger term (f c) occurs only in a literal that is assigned (by a
; decision) but is not needed to satisfy the input, since A is true. Hence
; (f c) is not admitted for matching, and we do not find the instance x -> c.
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun P (U) Bool)
(declare-fun Q (U) Bool)
(declare-const c U)
(declare-const A Bool)
(declare-const B Bool)
(assert (or A B))
(assert (or A (P (f c))))
(assert (forall ((x U)) (! (Q x) :pattern ((f x)))))
(assert (not (Q c)))
(check-sat)
