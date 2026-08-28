import ProximityPrize.SubmissionLower.BCHKSLocatorPolynomialPairToCodeSpecialize6400
import ProximityPrize.SubmissionLower.BCHKSLocatorPairToCodeOwner6400

/-!
# Owner identities for the bivariate affine code component

This is the production interface consumed by the complementary-resultant
argument: every close owner specialization of the global bivariate code
component lies in the semilinear span of its two locator multipliers.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

open ProximityPrize.Benchmark

theorem score6400PolynomialLocatorPairToCode_map_eval_eq_owner
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (hqker : q ∈ LinearMap.ker
      (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin)
    (z : IRSProfile.Field)
    (A : Finset IRSProfile.Index) (P : IRSProfile.Field[X])
    (hAcard : 185364 ≤ A.card)
    (hPdegree : P.natDegree ≤ 131071)
    (hagree : ∀ i ∈ A,
      P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i) :
    (score6400PolynomialLocatorPairToCode f₀ f₁ q).map
        (Polynomial.evalRingHom z) =
      (score6400LocatorRelationPair (fun k => (q k).eval z)).1.1 * P +
        (score6400LocatorRelationPair (fun k => (q k).eval z)).2.1 *
          P.map koalaSexticFrobenius.toRingHom := by
  rw [score6400PolynomialLocatorPairToCode_map_eval]
  apply score6400LocatorPairToCode_eq_owner
  · exact score6400_eval_mem_locatorKernel_of_polynomial_mem_ker
      f₀ f₁ q hqker z
  · exact hAcard
  · exact hPdegree
  · exact hagree

/-- The same owner identity with both specialized multipliers displayed as
maps of their global bivariate versions. -/
theorem score6400PolynomialLocatorPairToCode_map_eval_eq_owner_mapped
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (hqker : q ∈ LinearMap.ker
      (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin)
    (z : IRSProfile.Field)
    (A : Finset IRSProfile.Index) (P : IRSProfile.Field[X])
    (hAcard : 185364 ≤ A.card)
    (hPdegree : P.natDegree ≤ 131071)
    (hagree : ∀ i ∈ A,
      P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i) :
    (score6400PolynomialLocatorPairToCode f₀ f₁ q).map
        (Polynomial.evalRingHom z) =
      (score6400PolynomialLocatorRelationPair q).1.1.map
          (Polynomial.evalRingHom z) * P +
        (score6400PolynomialLocatorRelationPair q).2.1.map
            (Polynomial.evalRingHom z) *
          P.map koalaSexticFrobenius.toRingHom := by
  rw [score6400PolynomialLocatorRelationPair_fst_map_eval,
    score6400PolynomialLocatorRelationPair_snd_map_eval]
  exact score6400PolynomialLocatorPairToCode_map_eval_eq_owner
    f₀ f₁ q hqker z A P hAcard hPdegree hagree

end ProximityPrize.SubmissionLower
