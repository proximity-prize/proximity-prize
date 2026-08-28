import ProximityPrize.SubmissionLower.BCHKSLocatorPairOwnerDegree6400

/-!
# Pointwise agreement of the affine code and owner expressions
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

open ProximityPrize.Benchmark
open BCHKSExactSparsification6400

theorem score6400LocatorPairToCode_eval_eq_owner
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (u : PolynomialPairSpace IRSProfile.Field locatorOrdinaryRows6400
      locatorFrobeniusRows6400)
    (A : Finset IRSProfile.Index) (P : IRSProfile.Field[X])
    (hagree : ∀ i ∈ A,
      P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i)
    (i : IRSProfile.Index) (hi : i ∈ A) :
    (score6400LocatorPairToCode f₀ f₁ z u).eval
        (IRSProfile.domain i) =
      (u.1.1 * P +
        u.2.1 * P.map koalaSexticFrobenius.toRingHom).eval
          (IRSProfile.domain i) := by
  rw [score6400LocatorPairToCode_eval]
  simp only [Polynomial.eval_add, Polynomial.eval_mul]
  rw [polynomial_map_eval_of_fixed_locator koalaSexticFrobenius P
    (IRSProfile.domain i) (koalaSexticFrobenius_fixed_domain i),
    hagree i hi]

end ProximityPrize.SubmissionLower
