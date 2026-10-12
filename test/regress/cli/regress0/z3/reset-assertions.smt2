; COMMAND-LINE: --z3 --incremental
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: sat
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; reset-assertions recreates the ported context; each round must start clean.
(set-logic UF)
(declare-fun p () Bool)
(assert (and p (not p)))
(check-sat)
(reset-assertions)
(declare-fun q () Bool)
(assert (and q (not q)))
(check-sat)
(reset-assertions)
(declare-fun r () Bool)
(assert r)
(check-sat)
