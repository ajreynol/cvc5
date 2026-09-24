; COMMAND-LINE: --produce-proofs
; EXPECT: (error "Cannot eliminate subtypes from an input assumption with --strict-assumptions. Use --no-strict-assumptions to allow this.")
; EXIT: 1
; DISABLE-TESTER: dump
; DISABLE-TESTER: alethe
; Aliased bound variables make the CPC quant-unused-vars step invalid.
; DISABLE-TESTER: cpc
; REQUIRES: no-competition
; EXPECT-ERROR: Constructing a fresh variable for x since this symbol occurs in a let term that is present in the current context. Set fresh-binders to true or use -q to avoid this warning.
(set-logic ALL)
(assert (exists ((x Real))
          (let ((?y x))
          (and (<= 0 x) (exists ((x Real)) (forall ((v Real)) (> 0 ?y)))))))
(check-sat)
