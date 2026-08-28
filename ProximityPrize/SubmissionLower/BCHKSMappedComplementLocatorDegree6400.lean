import ProximityPrize.SubmissionLower.BCHKSMappedNodalCofactor6400

/-! # Degree of the challenge-constant complement locator -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem score6400_mappedComplementLocator_ne_zero
    (Fixed : Finset IRSProfile.Index) :
    (outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
        (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) ≠ 0 := by
  exact (Polynomial.map_ne_zero_iff Polynomial.C_injective).2
    (outsideAgreementLocator_ne_zero IRSProfile.domain Finset.univ Fixed)

theorem score6400_mappedComplementLocator_natDegree
    (Fixed : Finset IRSProfile.Index) :
    ((outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
      (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X])).natDegree =
        262144 - Fixed.card := by
  rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective,
    outsideAgreementLocator_natDegree, Finset.card_sdiff,
    Finset.inter_univ, Finset.card_univ]
  norm_num [IRSProfile.Index]

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
