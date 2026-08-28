import ProximityPrize.SubmissionLower.BCHKSGlobalResidualDegreeAbstract6400
import ProximityPrize.SubmissionLower.BCHKSReceivedBivariateDegree6400
import ProximityPrize.SubmissionLower.BCHKSFrobeniusBivariateSpecializationDegree6400

/-! # Outer degree of the concrete global received residual -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem score6400_globalResidual_natDegree_lt
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (A B C : IRSProfile.Field[X][X]) (d : Nat)
    (hA : A.natDegree ≤ d) (hB : B.natDegree ≤ d)
    (hC : C.natDegree < 262144 + d) :
    (A * score6400ReceivedBivariate f₀ f₁ +
      B * score6400FrobeniusReceivedBivariate f₀ f₁ - C).natDegree <
        262144 + d := by
  exact inhomogeneous_residual_natDegree_lt A B C
    (score6400ReceivedBivariate f₀ f₁)
    (score6400FrobeniusReceivedBivariate f₀ f₁)
    262144 d hA hB
    (score6400ReceivedBivariate_natDegree_lt f₀ f₁)
    (score6400FrobeniusReceivedBivariate_natDegree_lt f₀ f₁) hC

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
