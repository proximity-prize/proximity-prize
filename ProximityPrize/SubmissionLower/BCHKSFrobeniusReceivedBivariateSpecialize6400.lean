import ProximityPrize.SubmissionLower.BCHKSFrobeniusBivariateSpecializationNodes6400
import ProximityPrize.SubmissionLower.BCHKSLagrangeFixedMap6400

/-! # Safe specialization of the Frobenius received bivariate interpolator -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem score6400FrobeniusReceivedBivariate_map_eval_sealed
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) :
    (score6400FrobeniusReceivedBivariate f₀ f₁).map
        (Polynomial.evalRingHom z) =
      (score6400SealedReceivedInterpolator f₀ f₁ z).map
        koalaSexticFrobenius.toRingHom := by
  apply polynomial_eq_of_degree_lt_card_of_eval_eq
    Finset.univ (fun i : IRSProfile.Index ↦ IRSProfile.domain i)
    ((score6400FrobeniusReceivedBivariate f₀ f₁).map
      (Polynomial.evalRingHom z))
    ((score6400SealedReceivedInterpolator f₀ f₁ z).map
      koalaSexticFrobenius.toRingHom)
    IRSProfile.domain.injective.injOn
    (score6400FrobeniusReceivedBivariate_map_eval_degree_lt f₀ f₁ z)
    (score6400SealedReceivedInterpolator_map_frobenius_degree_lt f₀ f₁ z)
  intro i hi
  exact score6400Frobenius_specializations_eval_domain_eq f₀ f₁ z i

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
