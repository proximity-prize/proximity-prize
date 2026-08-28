import ProximityPrize.SubmissionLower.BCHKSGlobalInhomogeneousKeyEquation6400
import ProximityPrize.SubmissionLower.BCHKSFrobeniusReceivedBivariateSpecialize6400

/-! # Specialization of the owner-independent global quotient -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Embedding a base-field polynomial as challenge-constant coefficients and
then specializing the challenge recovers the original polynomial. -/
theorem map_C_map_eval
    {F : Type} [Field F] (P : F[X]) (z : F) :
    (P.map (Polynomial.C : F →+* F[X])).map
        (Polynomial.evalRingHom z) = P := by
  ext n
  simp

/-- The bivariate quotient specializes to the same complement-locator
factorization with the sealed received interpolator and its coefficientwise
Frobenius image. -/
theorem score6400_globalResidualQuotient_specialize
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (Fixed : Finset IRSProfile.Index)
    (A B C K : IRSProfile.Field[X][X])
    (hfactor :
      (outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
          (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) * K =
        A * score6400ReceivedBivariate f₀ f₁ +
          B * score6400FrobeniusReceivedBivariate f₀ f₁ - C)
    (z : IRSProfile.Field) :
    outsideAgreementLocator IRSProfile.domain Finset.univ Fixed *
          K.map (Polynomial.evalRingHom z) =
      A.map (Polynomial.evalRingHom z) *
          score6400SealedReceivedInterpolator f₀ f₁ z +
        B.map (Polynomial.evalRingHom z) *
          (score6400SealedReceivedInterpolator f₀ f₁ z).map
            koalaSexticFrobenius.toRingHom -
        C.map (Polynomial.evalRingHom z) := by
  have hmapped := congrArg
    (Polynomial.map (Polynomial.evalRingHom z)) hfactor
  simp only [Polynomial.map_mul, Polynomial.map_add,
    Polynomial.map_sub] at hmapped
  rw [map_C_map_eval,
    score6400ReceivedBivariate_map_eval_sealed,
    score6400FrobeniusReceivedBivariate_map_eval_sealed] at hmapped
  exact hmapped

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
