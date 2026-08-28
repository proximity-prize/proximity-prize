import ProximityPrize.SubmissionLower.BCHKSReceivedBivariateNodes6400

/-! # An opacity-safe name for the specialized received interpolator -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSErrorEvaluatorSemilinear6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- The ordinary received interpolator behind the same generic opacity
barrier as the bivariate interpolators. -/
noncomputable def score6400SealedReceivedInterpolator
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) : IRSProfile.Field[X] :=
  bchksInterpolationSeal (score6400ReceivedInterpolator f₀ f₁ z)

theorem score6400SealedReceivedInterpolator_eq
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) :
    score6400SealedReceivedInterpolator f₀ f₁ z =
      score6400ReceivedInterpolator f₀ f₁ z := by
  rw [score6400SealedReceivedInterpolator, bchksInterpolationSeal_def]

@[simp]
theorem score6400SealedReceivedInterpolator_eval
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) (i : IRSProfile.Index) :
    (score6400SealedReceivedInterpolator f₀ f₁ z).eval
        (IRSProfile.domain i) = f₀ i + z * f₁ i := by
  rw [score6400SealedReceivedInterpolator_eq,
    score6400ReceivedInterpolator_eval]

theorem score6400SealedReceivedInterpolator_natDegree_lt
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) :
    (score6400SealedReceivedInterpolator f₀ f₁ z).natDegree <
      262144 := by
  rw [score6400SealedReceivedInterpolator_eq]
  exact score6400ReceivedInterpolator_natDegree_lt f₀ f₁ z

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
