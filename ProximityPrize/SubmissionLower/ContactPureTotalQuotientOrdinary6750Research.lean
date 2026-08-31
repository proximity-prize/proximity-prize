import ProximityPrize.SubmissionLower.ContactLegacyTwoFactorEasy6750Research
import ProximityPrize.SubmissionLower.ContactRFreeFixedSelectedCombinerResearch

 









namespace ProximityPrize.SubmissionLower
namespace ContactPureTotalQuotientOrdinary6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactInterpolation ContactTranslation ContactFactorCaps
open ContactPrimeSeedIncidence
open ContactProperCutSeedCount
open ContactIdentityResidualGlobalFlagResearch
open ContactFlagBezout6543Research
open ContactIdentityCurveProvider6731Research
open ContactTightSingularLedgerResearch
open ContactTwoTailParameters6750Research
open ContactRouterCellCosts6750Research
open ContactAnchoredOrdinaryFixedCell6750Research
open ContactSelectedCount6750Research
open ContactSelectedOldCoreLowQuotients6750Research
open ContactLegacyTwoFactorEasy6750Research
open ContactRFreeFixedSelectedCombinerResearch

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev GlobalPoly := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : CharP K prime := by
  simpa [prime, ContactParameters6600Research.prime] using
    ContactFrozenAlignment6600Research.challenge_field_characteristic6600

 

 

theorem pureTotal_identity (t : Nat) :
    IdentityCellBudget6750 t 3 2 := by
  apply identityCellBudget_of_basis
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [identityCurveDegree, cellA, cellB, cellS,
      ContactRouterCellCosts6750Research.cellCostOf,
      cellFirstTail, cellSecondTail, cellSupport,
      ContactMovingAgreementCertificate6719Research.support,
      ContactAnchoredDelayedTailProviderAdapter6750Research.reducedResidualAgreementFlag6750,
      ContactAnchoredDelayedTailProviderAdapter6750Research.reducedAgreementDirection6750,
      ContactMovingOuterBudget6719Research.paddedCut,
      ContactMovingPositiveLedger6719Research.centreFlag,
      ContactMovingPositiveLedger6719Research.directionFlag,
      flagMixed, unitZFlag, unitYZFlag, unitAllFlag,
      ContactMovingPositiveLedger6719Research.surfaceFlag,
      ContactTwoTailParameters6750Research.n,
      ContactTwoTailParameters6750Research.w,
      ContactTwoTailParameters6750Research.errors,
      ContactTwoTailParameters6750Research.agreements,
      ContactTwoTailParameters6750Research.gap,
      add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all] <;>
    omega

 

theorem pureTotal_combinerGates
    {D t : Nat} (hDlo : 131072 ≤ D) (hDhi : D ≤ 8729952)
    (htlo : 3 ≤ t) (hthi : t ≤ 1706) :
    OrdinaryCellCombinerGatesD6750 D t 2 := by
  have hiy : (cellTightProfile D t 2).implicitYCap ≤ 199 := by
    simp only [cellTightProfile, TightParameters.implicitYCap,
      TightParameters.kappa, ContactTwoTailParameters6750Research.w]
    rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 131071)]
    omega
  have hac : (cellTightProfile D t 2).algebraicCap ≤ 5118 := by
    simp only [cellTightProfile, TightParameters.algebraicCap,
      TightParameters.kappa]
    omega
  have hmixed :
      2 * (cellTightProfile D t 2).implicitYCap *
          (cellTightProfile D t 2).algebraicCap < 2130706433 := by
    calc
      _ ≤ 2 * 199 * 5118 := by gcongr
      _ < 2130706433 := by norm_num
  refine ⟨by omega, by norm_num [ContactTwoTailParameters6750Research.prime],
    by norm_num [ContactTwoTailParameters6750Research.w],
    by norm_num [ContactTwoTailParameters6750Research.w,
      ContactTwoTailParameters6750Research.prime],
    ?_, by omega, ?_, ?_, ?_,
    by norm_num [ContactTwoTailParameters6750Research.w,
      ContactTwoTailParameters6750Research.agreements,
      ContactTwoTailParameters6750Research.n,
      ContactTwoTailParameters6750Research.errors],
    by norm_num [ContactTwoTailParameters6750Research.agreements,
      ContactTwoTailParameters6750Research.n]⟩
  · norm_num [ContactTwoTailParameters6750Research.w]
    omega
  · norm_num [ContactTwoTailParameters6750Research.prime]
    omega
  · exact hiy.trans_lt (by
      norm_num [ContactTwoTailParameters6750Research.prime])
  · exact hmixed

 

 

theorem factorOrdinaryArithmetic_of_pureTotal
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (F : GlobalPoly) (hdiv : F ∣ oldCommonCore S)
    (hYS : factorYS F = 0) (hS : factorS F = 0) :
    FactorOrdinaryArithmetic F := by
  have hcaps := factor_padded_caps_of_dvd_oldCore S F hdiv
  have hcontact := (factor_coords_le_of_dvd_oldCore S F hdiv).1
  have hr : factorPaddedR F = 2 := by
    simp [factorPaddedR, hS]
  have hy : factorPaddedY F = 3 := by
    simp [factorPaddedY, hr, hYS]
  have htlo : 3 ≤ factorPaddedT F := by
    simp only [factorPaddedT, hy]
    exact Nat.le_max_left _ _
  have hthi : factorPaddedT F ≤ 1706 := hcaps.1
  have hDlo : 131072 ≤ factorD F := by
    have h := factorD_short F
    norm_num [ContactTwoTailParameters6750Research.w] at h ⊢
    exact h
  have hDhi : factorD F ≤ 8729952 := by
    simp only [factorD]
    apply max_le
    · norm_num [ContactTwoTailParameters6750Research.w]
    · omega
  refine ⟨?_, ?_⟩
  · simpa only [hy, hr] using pureTotal_identity (factorPaddedT F)
  · simpa only [hr] using
      (pureTotal_combinerGates hDlo hDhi htlo hthi)

 
theorem factorZeroSeeds_card_le_pureTotal
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (F : GlobalPoly) (hF : F ≠ 0) (hdiv : F ∣ oldCommonCore S)
    (hYS : factorYS F = 0) (hS : factorS F = 0)
    (selected : K → Polynomial K) (Gamma Delta : Finset K)
    (hDelta : Delta ⊆ Gamma)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    (factorZeroSeeds F selected Delta).card ≤ factorEquationCost F := by
  have arithmetic := factorOrdinaryArithmetic_of_pureTotal
    S F hdiv hYS hS
  have hcount := factorZeroSeeds_card_le S F hF hdiv arithmetic
    selected Gamma Delta hDelta hdegree hagreement hnoPencil
  exact hcount

 

 



def factorRFreeCost (F : GlobalPoly) : Nat :=
  (cellTightProfile (factorD F) (max 1 (factorTotal F)) 1).countCap

theorem factor_degreeOf_R_eq_zero
    (F : GlobalPoly) (hS : factorS F = 0) :
    F.degreeOf (2 : Fin 4) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have hr := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [ContactFactorCaps.weight_fin4] at hr
  simp [residualSWeights] at hr
  change d 2 ≤ factorS F at hr
  omega

theorem factor_mem_rfree_box
    (F : GlobalPoly) (hS : factorS F = 0) :
    F ∈ ContactInterpolation.globalCoefficientBox K
      (factorD F) w (max 1 (factorTotal F)) 1 := by
  intro d hd
  have hc := MvPolynomial.le_weightedTotalDegree (contactWeights w) hd
  have ht := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  have hr := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [contact_weight] at hc
  rw [ContactFactorCaps.weight_fin4] at ht hr
  simp [residualTotalWeights, residualSWeights] at ht hr
  change d 0 + w * d 1 + (w - 1) * d 2 ≤ factorContact F at hc
  change d 1 + d 2 + d 3 ≤ factorTotal F at ht
  change d 2 ≤ factorS F at hr
  change d 1 + d 3 ≤ max 1 (factorTotal F) ∧
    d 2 ≤ 1 ∧ d 0 + w * d 1 + (w - 1) * d 2 < factorD F
  refine ⟨?_, ?_, ?_⟩
  · exact (by omega : d 1 + d 3 ≤ factorTotal F).trans
      (Nat.le_max_right _ _)
  · omega
  · exact hc.trans_lt ((Nat.lt_succ_self _).trans_le
      (Nat.le_max_right (w + 1) (factorContact F + 1)))

 
theorem factorRFree_combinerGates
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (F : GlobalPoly) (hdiv : F ∣ oldCommonCore S) :
    OrdinaryCellCombinerGatesD6750 (factorD F)
      (max 1 (factorTotal F)) 1 := by
  have hcoords := factor_coords_le_of_dvd_oldCore S F hdiv
  have hDlo := factorD_short F
  have hDhi : factorD F ≤ profileA.weightedCap := by
    have hc := hcoords.1
    simp only [factorD]
    apply max_le
    · norm_num [profileA,
        ContactTwoTailParameters6750Research.Profile.weightedCap, w,
        agreements, n, errors]
    · norm_num [profileA,
        ContactTwoTailParameters6750Research.Profile.weightedCap,
        agreements, n, errors] at ⊢
      omega
  have htlo : 1 ≤ max 1 (factorTotal F) := Nat.le_max_left _ _
  have hthi : max 1 (factorTotal F) ≤ 1706 := by
    exact max_le (by omega) hcoords.2.1
  exact combinerGatesD_of_bounds_analytic
    (factorD F) (max 1 (factorTotal F)) 1
    hDlo hDhi htlo (hthi.trans (by omega)) (by omega) (by omega)

 

theorem factorZeroSeeds_card_le_rfree
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (F : GlobalPoly) (hF : F ≠ 0) (hdiv : F ∣ oldCommonCore S)
    (hS : factorS F = 0)
    (selected : K → Polynomial K) (Gamma Delta : Finset K)
    (hDelta : Delta ⊆ Gamma)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    (factorZeroSeeds F selected Delta).card ≤ factorRFreeCost F := by
  let Zs := factorZeroSeeds F selected Delta
  have hZDelta : Zs ⊆ Delta := Finset.filter_subset _ _
  have hZGamma : Zs ⊆ Gamma := hZDelta.trans hDelta
  have gates := factorRFree_combinerGates S F hdiv
  have hsolution : ∀ gamma ∈ Zs,
      specialization K (selected gamma) gamma F = 0 := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2
  have hdegreeZ : ∀ gamma ∈ Zs,
      (selected gamma).natDegree ≤ w := by
    intro gamma hgamma
    exact hdegree gamma (hZGamma hgamma)
  have hagreementZ : ∀ gamma ∈ Zs, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card := by
    intro gamma hgamma
    exact hagreement gamma (hZGamma hgamma)
  have hnoPencilZ : NoLargeSelectedPencil selected Zs w errors :=
    noLargeSelectedPencil_mono selected Gamma Zs w errors hZGamma hnoPencil
  have hcount := global_count_le_tight_countCap_of_R_degree_zero
    (ordinaryProfileD (factorD F) (max 1 (factorTotal F)) 1)
    (cellTightProfile (factorD F) (max 1 (factorTotal F)) 1)
    (ordinaryAlignmentD (factorD F) (max 1 (factorTotal F)) 1)
    (prime := prime) F hF (factor_mem_rfree_box F hS)
    (factor_degreeOf_R_eq_zero F hS)
    gates.slope_pos gates.slope_lt_char gates.w_pos gates.w_lt_char
    gates.weighted_nontrivial gates.algebraic_pos gates.algebraic_lt_char
    gates.implicitY_lt_char gates.mixed_lt_char gates.w_lt_agreements
    gates.agreements_le_n selected Zs (Finset.univ : Finset I)
    IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
    (by change Fintype.card I = n; norm_num [I, n])
    hdegreeZ hsolution hagreementZ
    (by simpa [ordinaryProfileD,
      ContactRobustFixedMeet6656Research.Profile.errors,
      errors, agreements, n] using hnoPencilZ)
  simpa only [Zs, factorRFreeCost] using hcount

end
end ContactPureTotalQuotientOrdinary6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactPureTotalQuotientOrdinary6750Research.factorOrdinaryArithmetic_of_pureTotal
#print axioms ProximityPrize.SubmissionLower.ContactPureTotalQuotientOrdinary6750Research.factorZeroSeeds_card_le_pureTotal
#print axioms ProximityPrize.SubmissionLower.ContactPureTotalQuotientOrdinary6750Research.factorZeroSeeds_card_le_rfree
