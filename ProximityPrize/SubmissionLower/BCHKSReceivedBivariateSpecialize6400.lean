import ProximityPrize.SubmissionLower.BCHKSSealedReceivedInterpolator6400

/-! # Safe specialization of the ordinary received bivariate interpolator -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSErrorEvaluatorSemilinear6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem score6400ReceivedBivariate_map_eval_sealed
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) :
    (score6400ReceivedBivariate f₀ f₁).map
        (Polynomial.evalRingHom z) =
      score6400SealedReceivedInterpolator f₀ f₁ z := by
  rw [score6400SealedReceivedInterpolator_eq]
  have hmap := algebraLagrangeInterpolate_map_eval
    Finset.univ (fun i : IRSProfile.Index ↦ IRSProfile.domain i)
    (score6400ReceivedNode f₀ f₁) z
    IRSProfile.domain.injective.injOn Finset.univ_nonempty
  rw [score6400ReceivedBivariate, bchksInterpolationSeal_def]
  simpa only [score6400ReceivedInterpolator, score6400ReceivedNode,
    bchksInterpolationSeal_def, score6400ReceivedPolynomial_eval]
    using hmap

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
