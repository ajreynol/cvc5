; REQUIRES: safe-mode
; REQUIRES: no-competition
; DISABLE-TESTER: dump
; EXPECT: (error "Logic restricted in safe mode. Pool declarations are not supported in safe mode.")
; EXIT: 1
(set-logic ALL)
(declare-pool P Int (0 1))
