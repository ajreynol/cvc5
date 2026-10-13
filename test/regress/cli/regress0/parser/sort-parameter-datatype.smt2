; DISABLE-TESTER: dump
; SCRUBBER: grep -o "Global sort parameters are not permitted in datatype declarations"
; EXPECT: Global sort parameters are not permitted in datatype declarations
; EXIT: 1
(set-logic ALL)
(declare-sort-parameter A)
; Datatype declarations may use only their locally bound sort parameters.
(declare-datatype Box ((box (value A))))
