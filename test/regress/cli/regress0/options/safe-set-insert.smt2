; REQUIRES: safe-mode
; REQUIRES: no-competition
; EXPECT: (error "Logic restricted in safe mode. Cannot handle assertion with term of kind set.insert in this configuration.")
; EXIT: 1
(set-logic ALL)
(declare-const s (Set Int))
(assert (set.member 0 (set.insert 0 s)))
(check-sat)
