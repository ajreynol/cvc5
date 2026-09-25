; REQUIRES: unrestricted-mode
; COMMAND-LINE: --safe-mode=safe --check-proofs
; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic ALL)
(declare-fun s () (Set Int))
(assert (not (= s (as set.empty (Set Int)))))
(assert (not (set.member (set.choose s) s)))
(check-sat)
