import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSelectedCount6750Research
import ProximityPrize.SubmissionLower.ContactSelectedOldCoreLowQuotients6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredCanonicalHighSourceEndToEnd6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredThirdResidualAdapter6750Research

 









namespace ProximityPrize.SubmissionLower
namespace ContactLegacyCanonicalSource6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactTranslation
open ContactFactorCaps
open ContactFlagInterpolation6641Research
open ContactIdentityResidualGlobalFlagResearch
open ContactStackedSeedPartition6670Research
open ContactTwoTailParameters6750Research
open ContactNestedFiveCapCoefficientBox6750Research
open ContactAnchoredOneFamilySelector6750Research
open ContactAnchoredHighSourceHull6750Research
open ContactAnchoredCanonicalHighSourceEndToEnd6750Research
open ContactAnchoredThirdResidualAdapter6750Research
open ContactSelectedCount6750Research
open ContactSelectedOldCoreQuotientRank6750Research
open ContactSelectedOldCoreLowQuotients6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev GlobalPoly := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

 
def globalCoefficientArray
    (D w0 L s : Nat) (P : GlobalPoly) : CoefficientIndex D w0 L s → K :=
  fun c ↦ MvPolynomial.coeff (columnExponent c) P

 

theorem reconstruct_globalCoefficientArray_eq_of_mem
    (D w0 L s : Nat) (P : GlobalPoly)
    (hP : P ∈ globalCoefficientBox K D w0 L s) :
    reconstruct K D w0 L s (globalCoefficientArray D w0 L s P) = P := by
  classical
  ext d
  by_cases hd : d ∈ globalExponents D w0 L s
  · change d 1 + d 2 + d 3 ≤ L ∧ d 2 ≤ s ∧
      d 0 + w0 * d 1 + (w0 - 1) * d 2 < D at hd
    let ci : Fin (L + 1) := ⟨d 1, by omega⟩
    let cj : Fin (s + 1) := ⟨d 2, by omega⟩
    have hz : d 3 < L + 1 - ci.val - cj.val := by
      dsimp only [ci, cj]
      omega
    have hx : d 0 < D - w0 * ci.val - (w0 - 1) * cj.val := by
      dsimp only [ci, cj]
      omega
    let c : CoefficientIndex D w0 L s :=
      ⟨ci, cj, ⟨d 3, hz⟩, ⟨d 0, hx⟩⟩
    have hc : columnExponent c = d := by
      ext i
      fin_cases i <;> simp [c, ci, cj, columnExponent]
    rw [← hc, reconstruct_coeff]
    rfl
  · have hPzero : MvPolynomial.coeff d P = 0 := by
      by_contra hne
      exact hd (hP (MvPolynomial.mem_support_iff.mpr hne))
    have hRmem := reconstruct_mem_globalCoefficientBox K D w0 L s
      (globalCoefficientArray D w0 L s P)
    have hRzero : MvPolynomial.coeff d
        (reconstruct K D w0 L s (globalCoefficientArray D w0 L s P)) = 0 := by
      by_contra hne
      exact hd (hRmem (MvPolynomial.mem_support_iff.mpr hne))
    rw [hRzero, hPzero]

 

theorem oldCommonCore_mem_fixedHighSourceBox
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1) :
    oldCommonCore S ∈ nestedFiveCapCoefficientBox K
      (48 * ContactAnchoredOneFamilySelector6750Research.agreements)
      131071 1706 66 14 := by
  intro d hd
  have ht := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  have hy := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  have hr := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  have hc := MvPolynomial.le_weightedTotalDegree (contactWeights 131071) hd
  have htCap := oldCommonCore_total_le S
  have hyCap := oldCommonCore_ys_le S
  have hrCap := oldCommonCore_slope_le S
  have hcCap := oldCommonCore_contact_le S
  change MvPolynomial.weightedTotalDegree residualTotalWeights
    (oldCommonCore S) ≤ 1706 at htCap
  change MvPolynomial.weightedTotalDegree residualYSWeights
    (oldCommonCore S) ≤ 66 at hyCap
  change MvPolynomial.weightedTotalDegree residualSWeights
    (oldCommonCore S) ≤ 14 at hrCap
  have ht' := ht.trans htCap
  have hy' := hy.trans hyCap
  have hr' := hr.trans hrCap
  have hc' := hc.trans hcCap
  change d 1 + d 2 + d 3 ≤ 1706 ∧ d 1 + d 2 ≤ 66 ∧
    d 2 ≤ 14 ∧
    d 0 + 131071 * d 1 + (131071 - 1) * d 2 <
      48 * ContactAnchoredOneFamilySelector6750Research.agreements
  rw [weight_fin4] at ht' hy' hr'
  rw [contact_weight] at hc'
  simp [residualTotalWeights, residualYSWeights, residualSWeights] at ht' hy' hr'
  norm_num [ContactAnchoredOneFamilySelector6750Research.agreements] at hc' ⊢
  omega

 

theorem oldCommonCore_mem_highGlobalBox
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1) :
    oldCommonCore S ∈ globalCoefficientBox K
      11458062 131071 familyMaxTotal 18 := by
  intro d hd
  have h := oldCommonCore_mem_fixedHighSourceBox S hd
  change d 1 + d 2 + d 3 ≤ familyMaxTotal ∧ d 2 ≤ 18 ∧
    d 0 + 131071 * d 1 + (131071 - 1) * d 2 < 11458062
  change d 1 + d 2 + d 3 ≤ 1706 ∧ d 1 + d 2 ≤ 66 ∧
    d 2 ≤ 14 ∧
    d 0 + 131071 * d 1 + (131071 - 1) * d 2 <
      48 * ContactAnchoredOneFamilySelector6750Research.agreements at h
  norm_num [familyMaxTotal,
    ContactAnchoredOneFamilySelector6750Research.agreements] at h ⊢
  omega

 
def oldCommonCoreHighArray {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) :
    CoefficientIndex 11458062 131071 familyMaxTotal 18 → K :=
  globalCoefficientArray 11458062 131071 familyMaxTotal 18 (oldCommonCore S)

theorem reconstruct_oldCommonCoreHighArray
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1) :
    reconstruct K 11458062 131071 familyMaxTotal 18
      (oldCommonCoreHighArray S) = oldCommonCore S := by
  exact reconstruct_globalCoefficientArray_eq_of_mem
    11458062 131071 familyMaxTotal 18 (oldCommonCore S)
      (oldCommonCore_mem_highGlobalBox S)

 

def fixedHighSourceCertificate_of_oldCommonCore
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    FixedHighSourceCertificate (oldCommonCoreHighArray S) selected
      (fixedSeeds selected Gamma S.QA S.QB S.QC) where
  source_ne_zero := by
    rw [reconstruct_oldCommonCoreHighArray]
    exact oldCommonCore_ne_zero S
  source_mem_fiveCap := by
    rw [reconstruct_oldCommonCoreHighArray]
    exact oldCommonCore_mem_fixedHighSourceBox S
  source_vanishes := by
    intro gamma hgamma
    rw [reconstruct_oldCommonCoreHighArray]
    exact fixedSeeds_vanish selected Gamma S.QA S.QB S.QC gamma hgamma

end

end ContactLegacyCanonicalSource6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactLegacyCanonicalSource6750Research.reconstruct_oldCommonCoreHighArray
#print axioms ProximityPrize.SubmissionLower.ContactLegacyCanonicalSource6750Research.fixedHighSourceCertificate_of_oldCommonCore
