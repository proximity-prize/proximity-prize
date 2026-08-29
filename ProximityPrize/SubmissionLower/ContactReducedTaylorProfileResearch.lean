import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSharpTaylorFixedMeet6656Research
import ProximityPrize.SubmissionLower.ContactReducedTaylorWeights6643Research
import ProximityPrize.SubmissionLower.ContactCongruentCuts6643Research

namespace ProximityPrize.SubmissionLower.ContactReducedTaylorProfileResearch

open ContactGenericSurface ContactPolynomialSolutions ContactTaylorNumerators
open ContactPrimeSeedIncidence ContactIdentityResidualGlobalFlagResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactFlagBezout6543Research ContactResidualSupportParametersResearch
open ContactReducedTaylorNumerators6643Research
open ContactCongruentCuts6643Research

noncomputable section

variable {K Omega : Type} [Field K] [Field Omega]

/-- The reduced representative moves the saved pure-`R` unit into the
middle flag coordinate, leaving both cumulative facets unchanged. -/
def reducedAgreementDirection (P : ResidualSupportParameters) : FlagDegree :=
  ⟨2 * (P.total - P.ys), 2 * (P.ys - P.s), 2 * P.s - 2⟩

def reducedResidualAgreementFlag
    (P : ResidualSupportParameters) (d : ℕ) : FlagDegree :=
  ⟨(reducedAgreementDirection P).zOnly * d,
    1 + (reducedAgreementDirection P).yz * d,
    (reducedAgreementDirection P).all * d⟩

theorem reducedResidualAgreementFlag_ys
    (P : ResidualSupportParameters) (d : ℕ) :
    (reducedResidualAgreementFlag P d).yz +
        (reducedResidualAgreementFlag P d).all =
      1 + d * (2 * P.ys - 2) := by
  have hs := P.s_le_ys
  have h1 := P.one_le_s
  have hcoeff :
      2 * (P.ys - P.s) + (2 * P.s - 2) = 2 * P.ys - 2 := by
    rw [Nat.mul_sub_left_distrib]
    omega
  simp only [reducedResidualAgreementFlag, reducedAgreementDirection]
  rw [← hcoeff]
  ring

theorem reducedResidualAgreementFlag_total
    (P : ResidualSupportParameters) (d : ℕ) :
    (reducedResidualAgreementFlag P d).zOnly +
        (reducedResidualAgreementFlag P d).yz +
        (reducedResidualAgreementFlag P d).all =
      1 + d * (2 * P.total - 2) := by
  have hs := P.s_le_ys
  have ht := P.ys_le_total
  have h1 := P.one_le_s
  have hcoeff : 2 * (P.total - P.ys) + 2 * (P.ys - P.s) +
      (2 * P.s - 2) = 2 * P.total - 2 := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
    omega
  simp only [reducedResidualAgreementFlag, reducedAgreementDirection]
  rw [← hcoeff]
  ring

def reducedAgreementPolynomial (phi : Polynomial K →+* Omega)
    (P : ResidualSupportParameters) (F : MvPolynomial (Fin 4) K)
    (d : ℕ) (x u0 u1 : K) : MvPolynomial (Fin 3) Omega :=
  surfaceMap phi (reducedAgreementNumerator F P.s d
    (fun j ↦ (j.factorial : K)⁻¹) x u0 u1)

theorem agreementPolynomial_sub_reduced_dvd
    (phi : Polynomial K →+* Omega) (P : ResidualSupportParameters)
    (F : MvPolynomial (Fin 4) K) (d : ℕ) (x u0 u1 : K) :
    surfaceMap phi F ∣ agreementPolynomial phi F d x u0 u1 -
      reducedAgreementPolynomial phi P F d x u0 u1 := by
  change surfaceMap phi F ∣
    surfaceMap phi (agreementNumerator F d
      (fun j ↦ (j.factorial : K)⁻¹) x u0 u1) -
    surfaceMap phi (reducedAgreementNumerator F P.s d
      (fun j ↦ (j.factorial : K)⁻¹) x u0 u1)
  rw [← map_sub]
  exact map_dvd (surfaceMap phi)
    (agreementNumerator_sub_reduced_dvd F P.s d
      (fun j ↦ (j.factorial : K)⁻¹) x u0 u1)

theorem surfaceMap_reducedAgreement_in_flag
    (phi : Polynomial K →+* Omega) (P : ResidualSupportParameters)
    {F : MvPolynomial (Fin 4) K} (H : ResidualSupportData P F)
    (d : ℕ) (coeffs : ℕ → K) (x u0 u1 : K) :
    PolynomialInFlag (reducedResidualAgreementFlag P d)
      (surfaceMap phi
        (reducedAgreementNumerator F P.s d coeffs x u0 u1)) := by
  have hR := reducedAgreementNumerator_R_degree_bound F P.s P.one_le_s
    H.coordinate_bounds.2.1 d coeffs x u0 u1
  have hYS := reducedAgreementNumerator_wt_le residualYSWeights rfl rfl rfl
    F P.s P.ys P.one_le_s P.two_le_ys H.ys_weight d coeffs x u0 u1
  have hTotal := reducedAgreementNumerator_wt_le residualTotalWeights rfl rfl rfl
    F P.s P.total P.one_le_s (P.two_le_ys.trans P.ys_le_total)
    H.total_weight d coeffs x u0 u1
  rw [show residualYSWeights 3 = 0 from rfl] at hYS
  rw [show residualTotalWeights 3 = 1 from rfl] at hTotal
  norm_num at hYS hTotal
  intro e he
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp
    (support_surfaceMap_subset phi
      (reducedAgreementNumerator F P.s d coeffs x u0 u1) he)
  have hqR := (MvPolynomial.monomial_le_degreeOf (2 : Fin 4) hq).trans hR
  have hqYS :=
    (MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hYS
  have hqTotal :=
    (MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans hTotal
  rw [ContactFactorCaps.weight_fin4] at hqYS hqTotal
  change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 0 ≤ _ at hqYS
  change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 1 ≤ _ at hqTotal
  norm_num at hqYS hqTotal
  change q 2 ≤ (reducedResidualAgreementFlag P d).all ∧
    q 1 + q 2 ≤ (reducedResidualAgreementFlag P d).yz +
      (reducedResidualAgreementFlag P d).all ∧
    q 1 + q 2 + q 3 ≤ (reducedResidualAgreementFlag P d).zOnly +
      (reducedResidualAgreementFlag P d).yz +
      (reducedResidualAgreementFlag P d).all
  refine ⟨?_, ?_, ?_⟩
  · change q 2 ≤ (2 * P.s - 2) * d
    have hs : 2 * (P.s - 1) = 2 * P.s - 2 := by omega
    have heq : 2 * d * (P.s - 1) = (2 * P.s - 2) * d := by
      rw [← hs]
      ring
    rw [heq] at hqR
    exact hqR
  · rw [reducedResidualAgreementFlag_ys]
    have hs : 2 * (P.ys - 1) = 2 * P.ys - 2 := by omega
    have heq : 2 * d * (P.ys - 1) = d * (2 * P.ys - 2) := by
      rw [← hs]
      ring
    rw [heq] at hqYS
    exact hqYS
  · rw [reducedResidualAgreementFlag_total]
    have hs : 2 * (P.total - 1) = 2 * P.total - 2 := by
      have := P.one_le_s.trans (P.s_le_ys.trans P.ys_le_total)
      omega
    have heq : 2 * d * (P.total - 1) = d * (2 * P.total - 2) := by
      rw [← hs]
      ring
    rw [heq] at hqTotal
    exact hqTotal

theorem agreement_in_flag_mod_factor
    (phi : Polynomial K →+* Omega) (P : ResidualSupportParameters)
    {F : MvPolynomial (Fin 4) K} (H : ResidualSupportData P F)
    (G : MvPolynomial (Fin 3) Omega) (hG : G ∣ surfaceMap phi F)
    (d : ℕ) (x u0 u1 : K) :
    PolynomialInFlagMod (Ideal.span {G}) (reducedResidualAgreementFlag P d)
      (agreementPolynomial phi F d x u0 u1) := by
  refine ⟨reducedAgreementPolynomial phi P F d x u0 u1,
    surfaceMap_reducedAgreement_in_flag phi P H d
      (fun j ↦ (j.factorial : K)⁻¹) x u0 u1, ?_⟩
  exact Ideal.mem_span_singleton.mpr
    (hG.trans (agreementPolynomial_sub_reduced_dvd phi P F d x u0 u1))

theorem agreement_in_flag_mod_ideal
    (phi : Polynomial K →+* Omega) (P : ResidualSupportParameters)
    {F : MvPolynomial (Fin 4) K} (H : ResidualSupportData P F)
    (I : Ideal (MvPolynomial (Fin 3) Omega)) (hF : surfaceMap phi F ∈ I)
    (d : ℕ) (x u0 u1 : K) :
    PolynomialInFlagMod I (reducedResidualAgreementFlag P d)
      (agreementPolynomial phi F d x u0 u1) := by
  refine ⟨reducedAgreementPolynomial phi P F d x u0 u1,
    surfaceMap_reducedAgreement_in_flag phi P H d
      (fun j ↦ (j.factorial : K)⁻¹) x u0 u1, ?_⟩
  exact sub_mem_of_dvd I hF
    (agreementPolynomial_sub_reduced_dvd phi P F d x u0 u1)

end

end ProximityPrize.SubmissionLower.ContactReducedTaylorProfileResearch
