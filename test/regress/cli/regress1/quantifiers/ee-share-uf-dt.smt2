; COMMAND-LINE: --ee-share-uf-dt --user-pat=strict --no-cbqi
; COMMAND-LINE: --ee-share-uf-dt
; EXPECT: unsat
; A quantified problem in which the theories of UF and datatypes share terms:
; box and get are datatype-sorted uninterpreted functions, and the refutation
; needs E-matching, UF congruence, datatype injectivity and integer arithmetic
; together. With --ee-share-uf-dt the two theories use one equality engine.
(set-logic UFDTLIA)
(declare-datatype Poly ((PInt (uint Int)) (PBool (ubool Bool))))
(declare-datatype Opt ((None) (Some (val Poly))))
(declare-fun box (Int) Poly)
(declare-fun get (Int) Opt)
(declare-fun sz (Opt) Int)
(assert (forall ((n Int)) (! (= (box n) (PInt n)) :pattern ((box n)))))
(assert (forall ((n Int)) (! (= (sz (Some (PInt n))) n) :pattern ((sz (Some (PInt n)))))))
(assert (forall ((i Int)) (! (=> (>= i 0) (= (get i) (Some (box i)))) :pattern ((get i)))))
(declare-const a Int)
(declare-const b Int)
(declare-const p Poly)
(assert (>= a 0))
(assert (= (get a) (Some p)))
(assert (= (box b) p))
(assert (distinct a b))
(check-sat)
