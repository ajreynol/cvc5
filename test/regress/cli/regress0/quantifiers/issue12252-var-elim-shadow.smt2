; note: cpc reference checking not supported, cvc5 collapses singleton and/or applications when parsing, so the assumptions of the proof are not syntactically the assertions of this file
; DISABLE-TESTER: cpc
; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(assert (forall ((a Bool) (b Bool))                                          
(= (=> false true) (exists ((c Bool))                                                              
(and (=> a (or (and (= c b) (forall ((b Bool))                           
(and (= c (and a b))))))))))))                  
(check-sat)     
