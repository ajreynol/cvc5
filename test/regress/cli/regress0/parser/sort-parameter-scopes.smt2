; DISABLE-TESTER: dump
; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(push 1)
(declare-sort-parameter A)
(declare-const a A)
(pop 1)
; The local parameter is gone: this is an ordinary uninterpreted sort.
(declare-sort A 0)
(declare-const a A)
(assert (= a a))
(check-sat)
(reset-assertions)
; reset-assertions clears declarations at level zero as well.
(declare-sort-parameter A)
(declare-const a (Array Int A))
(check-sat)
(reset)
(set-logic QF_LIA)
(declare-sort-parameter A)
(check-sat)
