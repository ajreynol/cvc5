; COMMAND-LINE: --miniscope-quant=agg --no-cegqi-midpoint --rlimit=100000
; EXPECT: unknown
;
; This benchmark is satisfiable (it is equivalent to (> (* V K) 0.0)).
; Previously, we incorrectly answered unsat with the given options due to
; applying an inconsistent mix of virtual term elimination and free virtual
; term substitution when rewriting an instantiation. Note virtual term
; substitution is now disabled by default (--cegqi-midpoint is true by
; default), so --no-cegqi-midpoint is required to exercise this code path.
(set-logic NRA)
(declare-fun V () Real)
(declare-fun K () Real)
(assert
  (forall ((S Real) (S2 Real))
    (or (= S 0.0)
        (< S2 0.0)
        (<= S2 S)
        (> (* S2 V K) (* S V K)))))
(check-sat)
