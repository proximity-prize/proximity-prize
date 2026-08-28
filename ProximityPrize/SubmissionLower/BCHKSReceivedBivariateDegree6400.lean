import ProximityPrize.SubmissionLower.BCHKSReceivedBivariateNodes6400

/-! # Outer degree of the ordinary sealed received interpolator -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem score6400ReceivedBivariate_natDegree_lt
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) :
    (score6400ReceivedBivariate f₀ f₁).natDegree < 262144 := by
  rw [score6400ReceivedBivariate, bchksInterpolationSeal_def]
  have hdegree := algebraLagrangeInterpolate_natDegree_lt_card
    Finset.univ (fun i : IRSProfile.Index ↦ IRSProfile.domain i)
    (score6400ReceivedNode f₀ f₁)
    IRSProfile.domain.injective.injOn Finset.univ_nonempty
  have hcard : (Finset.univ : Finset IRSProfile.Index).card = 262144 := by
    norm_num [IRSProfile.Index]
  rw [hcard] at hdegree
  exact hdegree

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
