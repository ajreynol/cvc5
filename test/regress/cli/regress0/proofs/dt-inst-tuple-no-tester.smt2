; REQUIRES: unrestricted-mode
; COMMAND-LINE: --dump-proofs --proof-format=cpc
; SCRUBBER: grep -o -E 'unsat|:rule dt-inst|is tuple'
; EXPECT: unsat
; EXPECT: :rule dt-inst
;; Tuples have a single constructor, hence their tester is trivially true. The
;; premise of dt-inst is the constant true for tuples, so that (is tuple x)
;; does not appear in the proof, which the scrubber above checks for. Note the
;; cpc tester does not apply to this test, since its expected output is not
;; plain unsat. The tuple case of dt-inst is checked with ethos by
;; regress0/datatypes/tuple-update-elim.smt2.
(set-logic ALL)
(set-option :produce-proofs true)
(declare-fun x () (Tuple Int Int))
(assert (= ((_ tuple.select 0) x) 1))
(assert (= ((_ tuple.select 1) x) 2))
(assert (not (= x (tuple 1 2))))
(check-sat)
