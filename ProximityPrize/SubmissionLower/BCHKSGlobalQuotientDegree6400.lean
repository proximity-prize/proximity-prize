import ProximityPrize.SubmissionLower.BCHKSGlobalInhomogeneousKeyEquation6400
import ProximityPrize.SubmissionLower.BCHKSGlobalResidualDegree6400
import ProximityPrize.SubmissionLower.BCHKSMappedComplementLocatorDegree6400

/-! # Locator-degree of the owner-independent quotient -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- If the global quotient is nonzero, its locator degree is strictly below
the sum of the fixed-set size and the primitive-direction degree. -/
theorem score6400_globalResidualQuotient_natDegree_lt
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (Fixed : Finset IRSProfile.Index)
    (A B C K : IRSProfile.Field[X][X]) (d : Nat)
    (hA : A.natDegree ≤ d) (hB : B.natDegree ≤ d)
    (hC : C.natDegree < 262144 + d)
    (hK : K ≠ 0)
    (hfactor :
      (outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
          (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) * K =
        A * score6400ReceivedBivariate f₀ f₁ +
          B * score6400FrobeniusReceivedBivariate f₀ f₁ - C) :
    K.natDegree < Fixed.card + d := by
  have hdegree := congrArg Polynomial.natDegree hfactor
  rw [Polynomial.natDegree_mul
    (score6400_mappedComplementLocator_ne_zero Fixed) hK,
    score6400_mappedComplementLocator_natDegree Fixed] at hdegree
  have hresidual := score6400_globalResidual_natDegree_lt
    f₀ f₁ A B C d hA hB hC
  omega

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
