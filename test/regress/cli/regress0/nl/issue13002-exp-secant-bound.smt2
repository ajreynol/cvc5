; REQUIRES: unrestricted-mode
; DISABLE-TESTER: model
; EXPECT: sat
;
; The polynomial approximation used as an upper bound for exp at positive
; arguments is P[x]/(1-x^n/n!), which over-approximates exp only where its
; denominator is positive. Its degree was chosen so that this holds at the
; center of the secant planes, but the upper secant point was taken to be
; center+1, which can fall outside of that range. Here this produced the
; unsound lemma (=> (<= 1.0 v 2.0) (<= (exp v) s)) where s is a secant that is
; negative on most of [1.0,2.0], and hence the wrong answer unsat.
;
; The model tester is disabled since checking the model of a sat answer for a
; transcendental term with a non-constant argument does not terminate here,
; independently of the above.
(set-logic ALL)
(declare-fun v () Real)
(assert (< v 2.0))
(assert (> (+ (sin v) (exp v)) 6.0))
(check-sat)
