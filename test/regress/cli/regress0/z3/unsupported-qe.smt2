; COMMAND-LINE: --z3
; COMMAND-LINE: --z3 --z3-slots=quantifiers
; COMMAND-LINE: --z3 --z3-slots=quantifiers --no-z3-shadow-plugins
; COMMAND-LINE: --z3 --z3-prop-engine=z3 --z3-preset=z3
; EXPECT: (error "get-qe is not supported by the selected search engine")
; EXIT: 1
; DISABLE-TESTER: model
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: dump
; The supported surface of --z3 is deliberately minimal; see
; src/z3/README.md. Refusing is the point: answering would use cvc5's
; own engines, which --z3 leaves constructed but inactive and which
; have therefore seen none of the assertions.
(set-logic LIA)
(declare-fun y () Int)
(get-qe (exists ((x Int)) (and (> x 0) (= y (* 2 x)))))
