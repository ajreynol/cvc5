; COMMAND-LINE: --re-loop-abstract=lazy
; COMMAND-LINE: --re-loop-abstract=eager
; COMMAND-LINE:
; EXPECT: unsat
(set-logic QF_SLIA)
(set-option :strings-exp true)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () String)
; The body of the loop does not have a fixed length, hence the loop is not
; eliminated by the rewriter. The over-approximation of the loop by re.* is
; satisfiable, hence this requires refinement at last call effort.
(assert (str.in_re x ((_ re.loop 3 3) (re.union (re.range "a" "b") (str.to_re "cccc")))))
(assert (= (str.len x) 4))
; The negated membership is not constrained at all until last call effort.
(assert (not (str.in_re y ((_ re.loop 2 3) (re.union (re.range "a" "b") (str.to_re "cc"))))))
(assert (str.in_re y (re.* (re.range "a" "b"))))
(assert (= (str.len y) 2))
(check-sat)
