; COMMAND-LINE: --re-loop-abstract=lazy
; COMMAND-LINE: --re-loop-abstract=eager
; COMMAND-LINE:
; EXPECT: sat
(set-logic QF_SLIA)
(set-option :strings-exp true)
(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
; fixed length body, rewritten to re.* plus length constraints
(assert (str.in_re x ((_ re.loop 3 5) (re.range "a" "z"))))
(assert (= (str.len x) 4))
; non-fixed length body, requires refinement to find a model
(assert (str.in_re y ((_ re.loop 2 2) (re.union (re.range "a" "b") (str.to_re "cc")))))
(assert (= (str.len y) 3))
; a loop beneath re.comp, which is over-approximated by re.none
(assert (str.in_re z (re.comp ((_ re.loop 2 3) (re.union (re.range "a" "b") (str.to_re "cc"))))))
(assert (str.in_re z (re.* (re.range "a" "b"))))
(assert (= (str.len z) 1))
(check-sat)
