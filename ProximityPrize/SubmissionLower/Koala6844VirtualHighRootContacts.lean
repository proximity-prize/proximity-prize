import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Taylor
import ProximityPrize.SubmissionLower.Koala6844VirtualHighContact



namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped BigOperators
open Polynomial

section Translation

variable {R : Type*} [CommRing R]

theorem mem_germ_ideal_of_taylor_mem
    (r : R) (l m : ℕ) (q F : Polynomial R)
    (h : Polynomial.taylor r F ∈
      Ideal.span ({X^l, Polynomial.taylor r q} : Set (Polynomial R)) ^ m) :
    F ∈ Ideal.span ({(X-C r)^l, q} : Set (Polynomial R)) ^ m := by
  let τ := Polynomial.taylorEquiv r
  let φ := τ.symm.toRingEquiv.toRingHom
  have hinverse (P : Polynomial R) : φ (Polynomial.taylor r P) = P := τ.symm_apply_apply P
  have hx : φ X = X-C r := by
    change τ.symm X = _
    rw [Polynomial.taylorEquiv_symm]
    change Polynomial.taylor (-r) X = _
    rw [Polynomial.taylor_X, map_neg, sub_eq_add_neg]
  have image := Ideal.mem_map_of_mem φ h
  rw [Ideal.map_pow, Ideal.map_span, hinverse] at image
  simpa only [Set.image_insert_eq, Set.image_singleton, map_pow, hx, hinverse] using image

end Translation

section SplitDivisor

variable {K : Type*} [Field K] [DecidableEq K]


end SplitDivisor

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
