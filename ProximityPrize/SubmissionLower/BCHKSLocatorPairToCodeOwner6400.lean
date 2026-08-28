import ProximityPrize.SubmissionLower.BCHKSLocatorPairOwnerEval6400
import ProximityPrize.SubmissionLower.BCHKSPolynomialAgreementIdentity6400

/-!
# Owner identity for the affine code component

This file isolates the concrete agreement-to-polynomial-identity argument
from the lower-cost construction and degree interface.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

open ProximityPrize.Benchmark
open BCHKSExactSparsification6400

/-- On any score-64 agreement witness, the interpolated affine component is
the expected semilinear expression in the owner polynomial. -/
theorem score6400LocatorPairToCode_eq_owner
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field)
    (hq : q ∈ LinearMap.ker
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).mulVecLin)
    (A : Finset IRSProfile.Index) (P : IRSProfile.Field[X])
    (hAcard : 185364 ≤ A.card)
    (hPdegree : P.natDegree ≤ 131071)
    (hagree : ∀ i ∈ A,
      P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i) :
    score6400LocatorPairToCode f₀ f₁ z
        (score6400LocatorRelationPair q) =
      (score6400LocatorRelationPair q).1.1 * P +
      (score6400LocatorRelationPair q).2.1 *
          P.map koalaSexticFrobenius.toRingHom := by
  let u := score6400LocatorRelationPair q
  let C := score6400LocatorPairToCode f₀ f₁ z u
  let R := u.1.1 * P +
    u.2.1 * P.map koalaSexticFrobenius.toRingHom
  have hCnat : C.natDegree < 185363 := by
    simpa only [C, u] using
      score6400LocatorPairToCode_natDegree_lt f₀ f₁ z q hq
  have hRnat : R.natDegree < 185363 := by
    simpa only [R, u] using
      locatorPairOwnerPolynomial_natDegree_lt u P hPdegree
  have hcard : 185363 ≤ A.card := hAcard.trans' (by norm_num)
  apply polynomial_eq_of_natDegree_lt_card_of_eval_index_eq
    C R A IRSProfile.domain IRSProfile.domain.injective.injOn
    (hCnat.trans_le hcard) (hRnat.trans_le hcard)
  intro i hi
  simpa only [C, R, u] using
    score6400LocatorPairToCode_eval_eq_owner f₀ f₁ z u A P hagree i hi

end ProximityPrize.SubmissionLower
