import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagKernelUniversalityResearch
import Mathlib.RingTheory.Derivation.MapCoeffs

 









namespace ProximityPrize.SubmissionLower
namespace ContactFlagKernelDerivativeContact6750Research

open scoped BigOperators
open Polynomial Module
open ContactFlagRankKernel6641Research
open ContactFlagInterpolation6641Research
open ContactFlagTranslation6641Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {K : Type*} [Field K]

 

def translatedRCoeffDerivation :
    Derivation K (Polynomial (Poly K)) (Polynomial (Poly K)) :=
  PolynomialModule.equivPolynomialSelf.compDer
    (MvPolynomial.pderiv (1 : Fin 3)).mapCoeffs

@[simp] theorem translatedRCoeffDerivation_coeff
    (H : Polynomial (Poly K)) (r : Nat) :
    (translatedRCoeffDerivation H).coeff r =
      MvPolynomial.pderiv (1 : Fin 3) (H.coeff r) := rfl

 

theorem translatedRCoeffDerivation_translationVariables
    (i : Fin 4) (x u0 u1 : K) :
    translatedRCoeffDerivation
        (translationVariables K x u0 u1 i) =
      homogenizedTranslation K x u0 u1
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.X i : MvPolynomial (Fin 4) K)) := by
  fin_cases i <;>
    simp [translatedRCoeffDerivation, translationVariables,
      homogenizedTranslation, ContactFlagInterpolation6641Research.seedAffine]

 

theorem translatedRCoeffDerivation_homogenizedTranslation
    (F : MvPolynomial (Fin 4) K) (x u0 u1 : K) :
    translatedRCoeffDerivation (homogenizedTranslation K x u0 u1 F) =
      homogenizedTranslation K x u0 u1
        (MvPolynomial.pderiv (2 : Fin 4) F) := by
  induction F using MvPolynomial.induction_on with
  | C c =>
      simp [translatedRCoeffDerivation, homogenizedTranslation]
  | add F G hF hG =>
      simp only [map_add, hF, hG]
  | mul_X F i hF =>
      have hXi :
          translatedRCoeffDerivation
              (homogenizedTranslation K x u0 u1
                (MvPolynomial.X i : MvPolynomial (Fin 4) K)) =
            homogenizedTranslation K x u0 u1
              (MvPolynomial.pderiv (2 : Fin 4)
                (MvPolynomial.X i : MvPolynomial (Fin 4) K)) := by
        simpa [homogenizedTranslation] using
          translatedRCoeffDerivation_translationVariables
            (K := K) i x u0 u1
      rw [map_mul, translatedRCoeffDerivation.leibniz, hF, hXi,
        MvPolynomial.pderiv_mul, map_add, map_mul, map_mul]
      ring

 


theorem slopeDifference_pow_pred_dvd_pderiv
    (f : Poly K) (n : Nat)
    (hdiv : slopeDifference K ^ n ∣ f) :
    slopeDifference K ^ (n - 1) ∣
      MvPolynomial.pderiv (1 : Fin 3) f := by
  obtain ⟨q, rfl⟩ := hdiv
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    refine ⟨(n : Poly K) *
        MvPolynomial.pderiv (1 : Fin 3) (slopeDifference K) * q +
          slopeDifference K * MvPolynomial.pderiv (1 : Fin 3) q, ?_⟩
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow]
    have hpow : slopeDifference K ^ n =
        slopeDifference K ^ (n - 1) * slopeDifference K := by
      rw [← pow_succ]
      congr
      omega
    rw [hpow]
    ring

 


theorem derivative_translated_contact
    (F : MvPolynomial (Fin 4) K) (x u0 u1 : K) (m : Nat)
    (hcontact : ∀ r : Nat,
      slopeDifference K ^ (m - r) ∣
        (homogenizedTranslation K x u0 u1 F).coeff r) :
    ∀ r : Nat, slopeDifference K ^ (m - 1 - r) ∣
      (homogenizedTranslation K x u0 u1
        (MvPolynomial.pderiv (2 : Fin 4) F)).coeff r := by
  intro r
  rw [← translatedRCoeffDerivation_homogenizedTranslation F x u0 u1,
    translatedRCoeffDerivation_coeff]
  have h := slopeDifference_pow_pred_dvd_pderiv
    ((homogenizedTranslation K x u0 u1 F).coeff r)
      (m - r) (hcontact r)
  have hexp : m - 1 - r = (m - r) - 1 := by omega
  simpa only [hexp] using h

end

end ContactFlagKernelDerivativeContact6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactFlagKernelDerivativeContact6750Research.translatedRCoeffDerivation_homogenizedTranslation
#print axioms ProximityPrize.SubmissionLower.ContactFlagKernelDerivativeContact6750Research.slopeDifference_pow_pred_dvd_pderiv
#print axioms ProximityPrize.SubmissionLower.ContactFlagKernelDerivativeContact6750Research.derivative_translated_contact
