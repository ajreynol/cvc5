; note: cpc reference checking not supported, the n-ary form of set.insert used here has no Eunoia equivalent, the signature declares it over a typed list
; DISABLE-TESTER: cpc
; REQUIRES: unrestricted-mode
; EXPECT: unsat
; DISABLE-TESTER: lfsc
(set-logic ALL)
(set-option :sets-exp true)
(set-option :strings-eager-reg false)
(assert (forall ((x Int)) (or (> 0 x) (> x 4))))
(assert (set.subset (set.comprehension ((_x1 Real)) false (seq.unit false)) (set.insert (set.choose (set.comprehension ((_x1 Real)) false (seq.unit (= _x1 0.0)))) (set.comprehension ((_x1 Real)) false (seq.unit false)))))
(check-sat)
