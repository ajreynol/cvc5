; COMMAND-LINE: --z3 --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; Repeated check-sat with assertions in between is part of the supported
; surface of --z3; see src/z3/README.md.
(set-logic UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (or p q))
(check-sat)
(assert (not p))
(check-sat)
(assert (not q))
(check-sat)
