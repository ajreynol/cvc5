; COMMAND-LINE: --incremental
; EXPECT: sat
(set-logic ALL)
(set-option :global-declarations true)
(push 1)
(declare-sort-parameter A)
(pop 1)
(reset-assertions)
; The parameter remains in scope after both pop and reset-assertions.
(declare-const a A)
(declare-fun f ((Array Int A)) A)
(check-sat)
