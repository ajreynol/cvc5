; REQUIRES: unrestricted-mode
; COMMAND-LINE: --eager-e-matching --deep-restart=input -o deep-restart
; EXPECT: (deep-restart ((P f) (not x) (= f k)))
; EXPECT: sat
; A deep restart makes a new prop engine, and the core is made again, from the
; preprocessed input and the literals learned at level zero, among them
; (not x), from the instance of the quantified formula for k.
(set-logic ALL)
(declare-const x Bool)
(declare-fun b () Int)
(declare-fun f () String)
(declare-fun k () String)
(declare-fun P (String) Bool)
(assert (ite (distinct b 0) (= (str.++ k f) (str.++ k k)) x))
(assert (distinct true (= b 0)))
(assert (forall ((s String)) (! (=> (P s) (not x)) :pattern ((P s)))))
(assert (or x (P f)))
(assert (P k))
(check-sat)
