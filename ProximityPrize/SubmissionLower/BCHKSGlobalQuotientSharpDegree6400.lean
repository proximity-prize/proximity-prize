import ProximityPrize.SubmissionLower.BCHKSGlobalQuotientDegree6400

/-! # The shared quotient lies inside the Frobenius locator window -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- In the low primitive direction, the fixed-set cost and quotient-direction
degree recombine to the degree of the original Frobenius lane.  Thus every
nonzero shared quotient has locator degree below `22489`. -/
theorem score6400_globalResidualQuotient_natDegree_lt_frobeniusRows
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (Fixed : Finset IRSProfile.Index)
    (RawB RawC H A B C K : IRSProfile.Field[X][X])
    (hH : H ≠ 0) (hB : B ≠ 0) (hK : K ≠ 0)
    (hFixed : Fixed.card ≤ H.natDegree)
    (hAdirection : A.natDegree ≤ B.natDegree)
    (hBfactor : RawB = H * B)
    (hCfactor : RawC = H * C)
    (hRawBdegree : RawB.natDegree < locatorFrobeniusRows6400)
    (hRawCdegree : RawC.natDegree < 185363)
    (hglobal :
      (outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
          (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) * K =
        A * score6400ReceivedBivariate f₀ f₁ +
          B * score6400FrobeniusReceivedBivariate f₀ f₁ - C) :
    K.natDegree < locatorFrobeniusRows6400 := by
  have hCdegreeLe : C.natDegree ≤ RawC.natDegree :=
    right_factor_natDegree_le RawC H C hH hCfactor
  have hCdegree : C.natDegree < 262144 + B.natDegree := by omega
  have hKdegree := score6400_globalResidualQuotient_natDegree_lt
    f₀ f₁ Fixed A B C K B.natDegree
    hAdirection (Nat.le_refl _) hCdegree hK hglobal
  have hRawBdegreeEq := congrArg Polynomial.natDegree hBfactor
  rw [Polynomial.natDegree_mul hH hB] at hRawBdegreeEq
  omega

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
