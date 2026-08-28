import ProximityPrize.SubmissionLower.BCHKSGlobalQuotientSpecialization6400
import ProximityPrize.SubmissionLower.BCHKSCommonLocatorKeyEquation6400

/-!
# Exact owner equation from the global quotient

Every decoded owner uses the same specialized quotient `K_z`.  Its full
actual-error locator times `K_z` equals the fixed defect locator times the
owner's semilinear error evaluator.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSErrorEvaluatorSemilinear6400
open BCHKSErrorLocatorKeyEquation6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem score6400_globalOwner_errorLocator_keyEquation
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (Fixed E : Finset IRSProfile.Index)
    (A B C K : IRSProfile.Field[X][X])
    (z : IRSProfile.Field) (P D : IRSProfile.Field[X])
    (hglobal :
      (outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
          (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) * K =
        A * score6400ReceivedBivariate f₀ f₁ +
          B * score6400FrobeniusReceivedBivariate f₀ f₁ - C)
    (howner :
      C.map (Polynomial.evalRingHom z) =
        A.map (Polynomial.evalRingHom z) * P +
          B.map (Polynomial.evalRingHom z) *
            P.map koalaSexticFrobenius.toRingHom)
    (herrorFactor :
      outsideAgreementLocator IRSProfile.domain Finset.univ E * D =
        score6400ReceivedInterpolator f₀ f₁ z - P) :
    Lagrange.nodal E (fun i ↦ IRSProfile.domain i) *
          K.map (Polynomial.evalRingHom z) =
      Lagrange.nodal Fixed (fun i ↦ IRSProfile.domain i) *
        (A.map (Polynomial.evalRingHom z) * D +
          B.map (Polynomial.evalRingHom z) *
            D.map koalaSexticFrobenius.toRingHom) := by
  let W := score6400SealedReceivedInterpolator f₀ f₁ z
  let L := outsideAgreementLocator IRSProfile.domain Finset.univ E
  let Az := A.map (Polynomial.evalRingHom z)
  let Bz := B.map (Polynomial.evalRingHom z)
  let Cz := C.map (Polynomial.evalRingHom z)
  let Kz := K.map (Polynomial.evalRingHom z)
  have hW : W = score6400ReceivedInterpolator f₀ f₁ z := by
    simpa only [W] using
      score6400SealedReceivedInterpolator_eq f₀ f₁ z
  have herrorFactorSealed : L * D = W - P := by
    rw [hW]
    simpa only [L] using herrorFactor
  have hLmap : L.map koalaSexticFrobenius.toRingHom = L := by
    simpa only [L] using outsideAgreementLocator_map IRSProfile.domain
      koalaSexticFrobenius koalaSexticFrobenius_fixed_domain
      (Finset.univ : Finset IRSProfile.Index) E
  have hresidual :
      Az * W + Bz * W.map koalaSexticFrobenius.toRingHom - Cz =
        L * (Az * D + Bz * D.map koalaSexticFrobenius.toRingHom) := by
    exact inhomogeneous_residual_eq_agreement_mul_semilinear
      koalaSexticFrobenius L Az Bz Cz W P D hLmap
      herrorFactorSealed (by simpa only [Az, Bz, Cz] using howner)
  have hspecialized := score6400_globalResidualQuotient_specialize
    f₀ f₁ Fixed A B C K hglobal z
  have hcomplement :
      selectedErrorLocator IRSProfile.domain Fixed * Kz =
        selectedErrorLocator IRSProfile.domain E *
          (Az * D + Bz * D.map koalaSexticFrobenius.toRingHom) := by
    change outsideAgreementLocator IRSProfile.domain Finset.univ Fixed * Kz =
      outsideAgreementLocator IRSProfile.domain Finset.univ E *
        (Az * D + Bz * D.map koalaSexticFrobenius.toRingHom)
    calc
      outsideAgreementLocator IRSProfile.domain Finset.univ Fixed * Kz =
          Az * W + Bz * W.map koalaSexticFrobenius.toRingHom - Cz := by
            simpa only [W, Az, Bz, Cz, Kz] using hspecialized
      _ = outsideAgreementLocator IRSProfile.domain Finset.univ E *
          (Az * D + Bz * D.map koalaSexticFrobenius.toRingHom) := by
            simpa only [L] using hresidual
  simpa only [Az, Bz, Kz] using
    nodal_keyEquation_of_complement_factorization
      IRSProfile.domain E Fixed Kz
      (Az * D + Bz * D.map koalaSexticFrobenius.toRingHom)
      hcomplement

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
