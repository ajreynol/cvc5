; note: cpc reference checking not supported, bag.empty cannot be disambiguated when the input is parsed as a reference file
; DISABLE-TESTER: cpc
; REQUIRES: unrestricted-mode
(set-logic ALL)
(set-info :status unsat)
(declare-const x (Bag Bool))
(assert (> (bag.card (bag.inter_min x bag.empty)) (bag.card (bag.inter_min x bag.empty))))
(check-sat)
