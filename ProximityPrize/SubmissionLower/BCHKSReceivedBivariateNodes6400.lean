import ProximityPrize.SubmissionLower.BCHKSReceivedBivariate6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

theorem score6400ReceivedNode_eq
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (i : IRSProfile.Index) :
    score6400ReceivedNode f₀ f₁ i =
      score6400ReceivedPolynomial f₀ f₁ i := by
  rw [score6400ReceivedNode, bchksInterpolationSeal_def]

theorem score6400FrobeniusReceivedNode_eq
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (i : IRSProfile.Index) :
    score6400FrobeniusReceivedNode f₀ f₁ i =
      score6400FrobeniusReceivedPolynomial f₀ f₁ i := by
  rw [score6400FrobeniusReceivedNode, bchksInterpolationSeal_def]

theorem score6400ReceivedBivariate_eval_coordinate_wrapped
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (i : IRSProfile.Index) :
    (score6400ReceivedBivariate f₀ f₁).eval
        (Polynomial.C (IRSProfile.domain i)) =
      score6400ReceivedNode f₀ f₁ i := by
  rw [score6400ReceivedBivariate, bchksInterpolationSeal_def]
  exact algebraLagrangeInterpolate_eval_at_node
    Finset.univ (fun j : IRSProfile.Index ↦ IRSProfile.domain j)
    (score6400ReceivedNode f₀ f₁)
    IRSProfile.domain.injective.injOn (Finset.mem_univ i)

theorem score6400FrobeniusReceivedBivariate_eval_coordinate_wrapped
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (i : IRSProfile.Index) :
    (score6400FrobeniusReceivedBivariate f₀ f₁).eval
        (Polynomial.C (IRSProfile.domain i)) =
      score6400FrobeniusReceivedNode f₀ f₁ i := by
  rw [score6400FrobeniusReceivedBivariate, bchksInterpolationSeal_def]
  exact algebraLagrangeInterpolate_eval_at_node
    Finset.univ (fun j : IRSProfile.Index ↦ IRSProfile.domain j)
    (score6400FrobeniusReceivedNode f₀ f₁)
    IRSProfile.domain.injective.injOn (Finset.mem_univ i)

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
