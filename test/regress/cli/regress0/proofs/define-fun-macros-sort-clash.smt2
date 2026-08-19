; COMMAND-LINE: --proof-define-fun-macros --check-proofs
; DISABLE-TESTER: alethe
; EXPECT: unsat
; The name f is used for both a sort and a defined function, which are in
; separate namespaces in SMT-LIB but not in the proof output. Thus f cannot
; be printed as a macro definition in proofs.
(set-logic UFLIA)
(declare-sort f 0)
(declare-fun a () f)
(declare-fun g (f) Int)
(define-fun f ((x f)) Int (+ (g x) 1))
(assert (< (f a) (g a)))
(check-sat)
