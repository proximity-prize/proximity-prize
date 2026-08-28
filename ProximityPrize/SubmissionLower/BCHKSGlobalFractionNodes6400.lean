import ProximityPrize.SubmissionLower.BCHKSChallengeFractionMap6400
import ProximityPrize.SubmissionLower.BCHKSGlobalInhomogeneousKeyEquation6400
import ProximityPrize.SubmissionLower.BCHKSMappedBilinearNode6400

/-! # Fraction-field nodes for the global received residual -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSLocatorAffineMultiplierCompatibility6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSGlobalInhomogeneousKeyEquation6400

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem score6400_receivedBivariate_fraction_eval_coordinate
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (i : IRSProfile.Index) :
    ((score6400ReceivedBivariate f₀ f₁).map
        score6400ChallengeIota).eval
          (score6400ChallengeFractionDomain i) =
      score6400ChallengeIota (score6400ReceivedPolynomial f₀ f₁ i) := by
  rw [score6400ChallengeFractionDomain_apply,
    score6400ChallengeIota_eval_map,
    score6400ReceivedBivariate_eval_coordinate_wrapped,
    score6400ReceivedNode_eq]

theorem score6400_frobeniusReceivedBivariate_fraction_eval_coordinate
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (i : IRSProfile.Index) :
    ((score6400FrobeniusReceivedBivariate f₀ f₁).map
        score6400ChallengeIota).eval
          (score6400ChallengeFractionDomain i) =
      score6400ChallengeIota
        (score6400FrobeniusReceivedPolynomial f₀ f₁ i) := by
  rw [score6400ChallengeFractionDomain_apply,
    score6400ChallengeIota_eval_map,
    score6400FrobeniusReceivedBivariate_eval_coordinate_wrapped,
    score6400FrobeniusReceivedNode_eq]

/-- The complement of `Fixed` has no root at a coordinate inside `Fixed`,
and this remains true after embedding both coefficient levels into the
challenge fraction field. -/
theorem score6400_mappedComplement_fraction_eval_ne_zero
    (Fixed : Finset IRSProfile.Index) (i : IRSProfile.Index)
    (hi : i ∈ Fixed) :
    (((outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
          (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X])).map
        score6400ChallengeIota).eval
          (score6400ChallengeFractionDomain i) ≠ 0 := by
  rw [score6400ChallengeFractionDomain_apply]
  exact mapped_twice_eval_ne_zero
    (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X])
    score6400ChallengeIota Polynomial.C_injective
    (IsFractionRing.injective IRSProfile.Field[X]
      Score6400ChallengeFraction)
    (outsideAgreementLocator IRSProfile.domain Finset.univ Fixed)
    (IRSProfile.domain i)
    (outsideAgreementLocator_eval_ne_zero_of_mem
      IRSProfile.domain Finset.univ Fixed hi)

end BCHKSLocatorAffineMultiplierCompatibility6400
end ProximityPrize.SubmissionLower
