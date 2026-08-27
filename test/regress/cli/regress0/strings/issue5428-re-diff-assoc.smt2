; note: cpc reference checking not supported, the n-ary form of re.diff used here has no Eunoia equivalent
; DISABLE-TESTER: cpc
(set-logic QF_S)
(set-info :status unsat)
(assert (str.in_re "" (re.diff (re.* re.allchar) re.allchar (re.* re.allchar))))
(check-sat)
