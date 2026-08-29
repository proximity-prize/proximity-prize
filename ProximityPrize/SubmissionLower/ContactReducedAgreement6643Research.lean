import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactReducedTaylorWeights6643Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlagResearch
import ProximityPrize.SubmissionLower.ContactNearPencil6630FlagResearch
import ProximityPrize.SubmissionLower.ContactCongruentCuts6643Research

/-!
# Frozen reduced agreement representatives for the 66.75 row

The original agreement polynomial is not assigned a smaller support. A
polynomially congruent representative receives the smaller flag instead.
-/

namespace ProximityPrize.SubmissionLower.ContactReducedAgreement6643Research

open ContactReducedTaylorNumerators6643Research
open ContactGenericSurface ContactPolynomialSolutions ContactTaylorNumerators
open ContactPrimeSeedIncidence
open ContactFlagBezout6543Research ContactPost6464MinkowskiRecurrenceResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactNearPencil6630FlagResearch ContactCongruentCuts6643Research

noncomputable section
set_option maxHeartbeats 1200000
variable {K Omega : Type} [Field K] [Field Omega]

def reducedAgreementPolynomial (phi : Polynomial K →+* Omega)
    (F : MvPolynomial (Fin 4) K) (d : ℕ) (x u0 u1 : K) :
    MvPolynomial (Fin 3) Omega :=
  surfaceMap phi (reducedAgreementNumerator F 10 d
    (fun j ↦ (j.factorial : K)⁻¹) x u0 u1)

theorem surfaceMap_agreement_sub_reduced_dvd
    (phi : Polynomial K →+* Omega) (F : MvPolynomial (Fin 4) K)
    (d : ℕ) (coeffs : ℕ → K) (x u0 u1 : K) :
    surfaceMap phi F ∣
      surfaceMap phi (agreementNumerator F d coeffs x u0 u1) -
        surfaceMap phi (reducedAgreementNumerator F 10 d coeffs x u0 u1) := by
  rw [← map_sub]
  exact map_dvd (surfaceMap phi)
    (agreementNumerator_sub_reduced_dvd F 10 d coeffs x u0 u1)

theorem agreementPolynomial_sub_reduced_dvd
    (phi : Polynomial K →+* Omega) (F : MvPolynomial (Fin 4) K)
    (d : ℕ) (x u0 u1 : K) :
    surfaceMap phi F ∣ agreementPolynomial phi F d x u0 u1 -
      reducedAgreementPolynomial phi F d x u0 u1 :=
  surfaceMap_agreement_sub_reduced_dvd phi F d _ x u0 u1

theorem surfaceMap_reducedAgreement_in_flag
    (phi : Polynomial K →+* Omega) (F : MvPolynomial (Fin 4) K)
    (hS : wt residualSWeights F ≤ 10)
    (hYS : wt residualYSWeights F ≤ 48)
    (hTotal : wt residualTotalWeights F ≤ 825)
    (d : ℕ) (coeffs : ℕ → K) (x u0 u1 : K) :
    PolynomialInFlag (residualAgreementFlag6630 d)
      (surfaceMap phi (reducedAgreementNumerator F 10 d coeffs x u0 u1)) := by
  have hR : F.degreeOf (2 : Fin 4) ≤ 10 := by
    have hw : residualSWeights = Pi.single (2 : Fin 4) 1 := by
      funext i
      fin_cases i <;> rfl
    rw [hw, wt, MvPolynomial.weightedTotalDegree_piSingle] at hS
    exact hS
  have hr := reducedAgreementNumerator_R_degree_bound F 10 (by norm_num)
    hR d coeffs x u0 u1
  have hm := reducedAgreementNumerator_wt_le residualYSWeights rfl rfl rfl
    F 10 48 (by norm_num) (by norm_num) hYS d coeffs x u0 u1
  have ht := reducedAgreementNumerator_wt_le residualTotalWeights rfl rfl rfl
    F 10 825 (by norm_num) (by norm_num) hTotal d coeffs x u0 u1
  rw [show residualYSWeights 3 = 0 from rfl] at hm
  rw [show residualTotalWeights 3 = 1 from rfl] at ht
  norm_num at hr hm ht
  intro e he
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp
    (support_surfaceMap_subset phi
      (reducedAgreementNumerator F 10 d coeffs x u0 u1) he)
  have hqr := (MvPolynomial.monomial_le_degreeOf (2 : Fin 4) hq).trans hr
  have hqm := (MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hm
  have hqt := (MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans ht
  rw [ContactFactorCaps.weight_fin4] at hqm hqt
  change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 0 ≤ _ at hqm
  change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 1 ≤ _ at hqt
  norm_num at hqm hqt
  rw [residualAgreementFlag6630_value]
  change q 2 ≤ 18 * d ∧
    q 1 + q 2 ≤ (1 + 76 * d) + 18 * d ∧
    q 1 + q 2 + q 3 ≤ 1554 * d + (1 + 76 * d) + 18 * d
  omega

theorem agreement_in_flag_mod_surface
    (phi : Polynomial K →+* Omega) (F : MvPolynomial (Fin 4) K)
    (hS : wt residualSWeights F ≤ 10)
    (hYS : wt residualYSWeights F ≤ 48)
    (hTotal : wt residualTotalWeights F ≤ 825)
    (d : ℕ) (coeffs : ℕ → K) (x u0 u1 : K) :
    PolynomialInFlagMod (Ideal.span {surfaceMap phi F})
      (residualAgreementFlag6630 d)
      (surfaceMap phi (agreementNumerator F d coeffs x u0 u1)) := by
  refine ⟨surfaceMap phi (reducedAgreementNumerator F 10 d coeffs x u0 u1),
    surfaceMap_reducedAgreement_in_flag phi F hS hYS hTotal d coeffs x u0 u1, ?_⟩
  exact Ideal.mem_span_singleton.mpr
    (surfaceMap_agreement_sub_reduced_dvd phi F d coeffs x u0 u1)

theorem agreement_in_flag_mod_factor
    (phi : Polynomial K →+* Omega) (F : MvPolynomial (Fin 4) K)
    (G : MvPolynomial (Fin 3) Omega) (hG : G ∣ surfaceMap phi F)
    (hS : wt residualSWeights F ≤ 10)
    (hYS : wt residualYSWeights F ≤ 48)
    (hTotal : wt residualTotalWeights F ≤ 825)
    (d : ℕ) (coeffs : ℕ → K) (x u0 u1 : K) :
    PolynomialInFlagMod (Ideal.span {G}) (residualAgreementFlag6630 d)
      (surfaceMap phi (agreementNumerator F d coeffs x u0 u1)) :=
  PolynomialInFlagMod.of_surface_mem (Ideal.mem_span_singleton.mpr hG)
    (agreement_in_flag_mod_surface phi F hS hYS hTotal d coeffs x u0 u1)

end
end ProximityPrize.SubmissionLower.ContactReducedAgreement6643Research
