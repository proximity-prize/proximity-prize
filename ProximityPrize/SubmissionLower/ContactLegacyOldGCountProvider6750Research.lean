import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSelectedCountHighTRepair6750Research
import ProximityPrize.SubmissionLower.ContactLegacyTwoFactorEasy6750Research
import ProximityPrize.SubmissionLower.ContactPureTotalQuotientOrdinary6750Research
import ProximityPrize.SubmissionLower.ContactCanonicalHighSourceThirdNonzero6750Research
import ProximityPrize.SubmissionLower.ContactCanonicalHighSourceAnchoredCap6750Research
import ProximityPrize.SubmissionLower.ContactResidualValidity6750Research

 
















namespace ProximityPrize.SubmissionLower
namespace ContactLegacyOldGCountProvider6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactTranslation
open ContactPrimeSeedIncidence
open ContactProperCutSeedCount
open ContactStackedSeedPartition6670Research
open ContactCommonCoreBranchPartition6750Research
open ContactTwoTailParameters6750Research
open ContactTwoTailResidualGeneric6750Research
open ContactRouterCellCosts6750Research
open ContactAnchoredOrdinaryFixedCell6750Research
open ContactOrdinaryHardShell6750Research
open ContactCanonicalHighSourceAnchoredCap6750Research
open ContactAnchoredHighSourceHull6750Research
open ContactAnchoredHighSourceAssembly6750Research
open ContactAnchoredCanonicalHighSourceEndToEnd6750Research
open ContactCanonicalHighSourceThirdNonzero6750Research
open ContactSelectedCount6750Research
open ContactSelectedCountHighTRepair6750Research
open ContactSelectedOldCoreLowQuotients6750Research
open ContactSelectedOldCoreQuotientRank6750Research
open ContactLegacyCanonicalSource6750Research
open ContactLegacyTwoFactorEasy6750Research
open ContactPureTotalQuotientOrdinary6750Research
open ContactResidualValidity6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 300000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev GlobalPoly := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

 

 


def canonicalZeroCost6750
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1) : Nat :=
  let H := canonicalOldCoreH S
  let t := factorTotal H
  let y := factorYS H
  let r := factorS H
  if OrdinaryHardCell t y r then
    canonicalAnchoredCost t y r
  else
    factorEquationCost H

 
def canonicalThirdCost6750
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1) : Nat :=
  let H := canonicalOldCoreH S
  (ContactAnchoredThirdResidual6750Research.thirdStage
      (factorTotal H) (factorYS H) (factorS H)).regularCountCap +
    (ContactAnchoredThirdResidual6750Research.thirdPivot
      (factorTotal H) (factorS H)).countCap

 



def canonicalNonzeroCost6750
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (F : CanonicalOldCoreFactorization S) : Nat :=
  if factorYS F.Q = 0 ∧ factorS F.Q = 0 then
    if factorTotal F.Q = 0 then
      factorEquationCost F.Q
    else
      factorRFreeCost F.Q
  else
    canonicalThirdCost6750 S

def legacyFixedCost6750
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (F : CanonicalOldCoreFactorization S) : Nat :=
  canonicalZeroCost6750 S + canonicalNonzeroCost6750 S F

 

 


def fixedCandidateSemantics_of_counts
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card) :
    FixedCandidateSemantics IRSProfile.domain u0 u1 selected
      (fixedSeeds selected Gamma S.QA S.QB S.QC) where
  support gamma := (Finset.univ : Finset I).filter (fun i ↦
    (selected gamma).eval (IRSProfile.domain i) =
      u0 i + gamma * u1 i)
  selected_degree gamma hgamma :=
    hdegree gamma (fixedSeeds_subset selected Gamma S.QA S.QB S.QC hgamma)
  agreement_card gamma hgamma :=
    hagreement gamma (fixedSeeds_subset selected Gamma S.QA S.QB S.QC hgamma)
  agreement_values gamma _ i hi := (Finset.mem_filter.mp hi).2

 

theorem commonCoreNonzeroSeeds_subset_factorZeroSeeds_Q
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (F : CanonicalOldCoreFactorization S)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    commonCoreNonzeroSeeds (canonicalOldCoreH S) selected
        (fixedSeeds selected Gamma S.QA S.QB S.QC) ⊆
      factorZeroSeeds F.Q selected
        (fixedSeeds selected Gamma S.QA S.QB S.QC) := by
  intro gamma hgamma
  have hfixed := commonCoreNonzeroSeeds_subset
    (canonicalOldCoreH S) selected
      (fixedSeeds selected Gamma S.QA S.QB S.QC) hgamma
  have hHnonzero := (Finset.mem_filter.mp hgamma).2
  have hGzero := fixedSeeds_vanish selected Gamma S.QA S.QB S.QC
    gamma hfixed
  have hmul : specialization K (selected gamma) gamma
      (canonicalOldCoreH S) *
      specialization K (selected gamma) gamma F.Q = 0 := by
    rw [← map_mul, ← F.factor_eq]
    exact hGzero
  have hQzero : specialization K (selected gamma) gamma F.Q = 0 := by
    rcases mul_eq_zero.mp hmul with hHzero | hQzero
    · exact False.elim (hHnonzero hHzero)
    · exact hQzero
  exact Finset.mem_filter.mpr ⟨hfixed, hQzero⟩

 
theorem commonCoreNonzeroSeeds_card_le_routed
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (F : CanonicalOldCoreFactorization S)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    (commonCoreNonzeroSeeds (canonicalOldCoreH S) selected
      (fixedSeeds selected Gamma S.QA S.QB S.QC)).card ≤
        canonicalNonzeroCost6750 S F := by
  let Delta := fixedSeeds selected Gamma S.QA S.QB S.QC
  have hDelta : Delta ⊆ Gamma :=
    fixedSeeds_subset selected Gamma S.QA S.QB S.QC
  have hQdiv : F.Q ∣ oldCommonCore S := by
    refine ⟨canonicalOldCoreH S, ?_⟩
    rw [mul_comm]
    exact F.factor_eq
  by_cases hpure : factorYS F.Q = 0 ∧ factorS F.Q = 0
  · by_cases htotal : factorTotal F.Q = 0
    · have hQcount := factorZeroSeeds_card_le_pureTotal
        S F.Q F.Q_ne_zero hQdiv hpure.1 hpure.2
          selected Gamma Delta hDelta hdegree hagreement hnoPencil
      have hsub := commonCoreNonzeroSeeds_subset_factorZeroSeeds_Q
        S F selected Gamma
      have hcard := (Finset.card_le_card hsub).trans hQcount
      rw [canonicalNonzeroCost6750, if_pos hpure, if_pos htotal]
      simpa only [Delta] using hcard
    · have hQcount := factorZeroSeeds_card_le_rfree
        S F.Q F.Q_ne_zero hQdiv hpure.2
          selected Gamma Delta hDelta hdegree hagreement hnoPencil
      have hsub := commonCoreNonzeroSeeds_subset_factorZeroSeeds_Q
        S F selected Gamma
      have hcard := (Finset.card_le_card hsub).trans hQcount
      rw [canonicalNonzeroCost6750, if_pos hpure, if_neg htotal]
      simpa only [Delta] using hcard
  · let source := fixedHighSourceCertificate_of_oldCommonCore
      S selected Gamma
    let semantics := fixedCandidateSemantics_of_counts
      S selected Gamma hdegree hagreement
    have hnoDelta : NoLargeSelectedPencil selected Delta w errors :=
      noLargeSelectedPencil_mono selected Gamma Delta w errors
        hDelta hnoPencil
    have hthird :=
      commonCoreNonzeroSeeds_card_le_of_canonicalHighSource_full_box
        u0 u1 (oldCommonCoreHighArray S) selected Delta
          source semantics hnoDelta
    have hthird' :
        (commonCoreNonzeroSeeds (canonicalOldCoreH S) selected Delta).card ≤
          canonicalThirdCost6750 S := by
      simpa only [canonicalThirdCost6750, canonicalOldCoreH,
        factorTotal, factorYS, factorS,
        ContactAnchoredCanonicalHighSourceEndToEnd6750Research.canonicalCoreTotal,
        ContactAnchoredCanonicalHighSourceEndToEnd6750Research.canonicalCoreYS,
        ContactAnchoredCanonicalHighSourceEndToEnd6750Research.canonicalCoreS]
        using hthird
    rw [canonicalNonzeroCost6750, if_neg hpure]
    simpa only [Delta] using hthird'

 

 

theorem factorCombinerGates_of_bounds
    (D t r : Nat) (hDlo : w + 1 ≤ D)
    (hDhi : D ≤ profileA.weightedCap)
    (htLo : 1 ≤ t) (htHi : t ≤ 1666)
    (hrLo : 1 ≤ r) (hrHi : r ≤ 14) :
    OrdinaryCellCombinerGatesD6750 D t r := by
  have hkLo : 1 ≤ 2 * r - 1 := by omega
  have hkHi : 2 * r - 1 ≤ 27 := by omega
  have hDnum : D ≤ 8548548 := by
    simpa [profileA, Profile.weightedCap, agreements, n, errors] using hDhi
  have hkD : (2 * r - 1) * D ≤ 27 * 8548548 :=
    Nat.mul_le_mul hkHi hDnum
  have himp : (cellTightProfile D t r).implicitYCap ≤ 1761 := by
    simp only [cellTightProfile,
      ContactTightSingularLedgerResearch.TightParameters.implicitYCap,
      ContactTightSingularLedgerResearch.TightParameters.kappa]
    rw [← Nat.lt_succ_iff]
    apply (Nat.div_lt_iff_lt_mul (by norm_num [w])).mpr
    norm_num [w]
    omega
  have halg : (cellTightProfile D t r).algebraicCap ≤ 44982 := by
    simp only [cellTightProfile,
      ContactTightSingularLedgerResearch.TightParameters.algebraicCap,
      ContactTightSingularLedgerResearch.TightParameters.kappa]
    exact (Nat.mul_le_mul hkHi htHi).trans (by norm_num)
  refine ⟨hrLo, hrHi.trans_lt (by norm_num [prime]),
    by norm_num [w], by norm_num [w, prime], ?_, htLo.trans ?_, ?_,
    himp.trans_lt (by norm_num [prime]), ?_,
    by norm_num [w, agreements, n, errors],
    by norm_num [agreements, n, errors]⟩
  · have hDw : w < D := by omega
    nlinarith
  · exact Nat.le_mul_of_pos_left _ hkLo
  · exact (Nat.mul_le_mul hkHi htHi).trans_lt (by norm_num [prime])
  · exact (Nat.mul_le_mul (Nat.mul_le_mul_left 2 himp) halg).trans_lt
      (by norm_num [prime])

 

theorem factorOrdinaryArithmetic_of_oldCoreDivisor
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (F : GlobalPoly) (hdiv : F ∣ oldCommonCore S) :
    FactorOrdinaryArithmetic F := by
  have hbasic := factor_padded_basic F
  have hcaps := factor_padded_caps_of_dvd_oldCore S F hdiv
  have hDlo := factorD_short F
  have hDhi : factorD F ≤ profileA.weightedCap := by
    have hc := (factor_coords_le_of_dvd_oldCore S F hdiv).1
    simp only [factorD]
    apply max_le
    · norm_num [w, profileA, Profile.weightedCap, agreements, n, errors]
    · norm_num [profileA, Profile.weightedCap, agreements, n, errors] at ⊢
      omega
  refine ⟨?_, ?_⟩
  · apply identityCellBudget_of_basis
    exact identityBasisBudget_of_basic_cell_analytic
        (factorPaddedT F) (factorPaddedY F) (factorPaddedR F)
        hbasic.1 hbasic.2.1 hbasic.2.2
  · exact factorCombinerGates_of_bounds
      (factorD F) (factorPaddedT F) (factorPaddedR F)
      hDlo hDhi (by omega) hcaps.1 (by omega) hcaps.2.2

 


theorem fixedSeeds_card_le_direct_oldCore
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    (fixedSeeds selected Gamma S.QA S.QB S.QC).card ≤
      factorEquationCost (oldCommonCore S) := by
  let Delta := fixedSeeds selected Gamma S.QA S.QB S.QC
  have hDelta : Delta ⊆ Gamma :=
    fixedSeeds_subset selected Gamma S.QA S.QB S.QC
  have hcount := factorZeroSeeds_card_le S (oldCommonCore S)
    (oldCommonCore_ne_zero S) (dvd_refl (oldCommonCore S))
    (factorOrdinaryArithmetic_of_oldCoreDivisor
      S (oldCommonCore S) (dvd_refl (oldCommonCore S)))
    selected Gamma Delta hDelta hdegree hagreement hnoPencil
  have hsub : Delta ⊆ factorZeroSeeds (oldCommonCore S) selected Delta := by
    intro gamma hgamma
    exact Finset.mem_filter.mpr
      ⟨hgamma, fixedSeeds_vanish selected Gamma S.QA S.QB S.QC gamma hgamma⟩
  exact (Finset.card_le_card hsub).trans hcount

 


def CanonicalZeroCountProvider6750 : Prop :=
  ∀ (u0 u1 : I → K) (S : SelectedInterpolants6750 u0 u1)
    (F : CanonicalOldCoreFactorization S)
    (selected : K → Polynomial K) (Gamma : Finset K),
    (∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w) →
    (∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card) →
    NoLargeSelectedPencil selected Gamma w errors →
    (commonCoreZeroSeeds (canonicalOldCoreH S) selected
      (fixedSeeds selected Gamma S.QA S.QB S.QC)).card ≤
        canonicalZeroCost6750 S

 

def CanonicalAnchoredZeroCountProvider6750 : Prop :=
  ∀ (u0 u1 : I → K) (S : SelectedInterpolants6750 u0 u1)
    (F : CanonicalOldCoreFactorization S)
    (selected : K → Polynomial K) (Gamma : Finset K),
    (∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w) →
    (∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card) →
    NoLargeSelectedPencil selected Gamma w errors →
    OrdinaryHardCell
      (factorTotal (canonicalOldCoreH S))
      (factorYS (canonicalOldCoreH S))
      (factorS (canonicalOldCoreH S)) →
    (commonCoreZeroSeeds (canonicalOldCoreH S) selected
      (fixedSeeds selected Gamma S.QA S.QB S.QC)).card ≤
        canonicalAnchoredCost
          (factorTotal (canonicalOldCoreH S))
          (factorYS (canonicalOldCoreH S))
          (factorS (canonicalOldCoreH S))

 


theorem canonicalZeroCountProvider6750_of_anchored
    (anchored : CanonicalAnchoredZeroCountProvider6750) :
    CanonicalZeroCountProvider6750 := by
  intro u0 u1 S F selected Gamma hdegree hagreement hnoPencil
  let H := canonicalOldCoreH S
  let Delta := fixedSeeds selected Gamma S.QA S.QB S.QC
  have hDelta : Delta ⊆ Gamma :=
    fixedSeeds_subset selected Gamma S.QA S.QB S.QC
  have hHdiv : H ∣ oldCommonCore S := ⟨F.Q, F.factor_eq⟩
  by_cases hhard : OrdinaryHardCell
      (factorTotal H) (factorYS H) (factorS H)
  · have hcount := anchored u0 u1 S F selected Gamma
      hdegree hagreement hnoPencil (by simpa only [H] using hhard)
    rw [canonicalZeroCost6750, if_pos hhard]
    simpa only [H, Delta] using hcount
  · have hcount := factorZeroSeeds_card_le S H F.H_ne_zero hHdiv
      (factorOrdinaryArithmetic_of_oldCoreDivisor S H hHdiv)
      selected Gamma Delta hDelta hdegree hagreement hnoPencil
    rw [canonicalZeroCost6750, if_neg hhard]
    simpa only [H, Delta, factorZeroSeeds, commonCoreZeroSeeds] using hcount

 


def LegacyOldGLedger6750 : Prop :=
  ∀ (u0 u1 : I → K) (S : SelectedInterpolants6750 u0 u1)
    (F : CanonicalOldCoreFactorization S),
    OrdinaryHardCell (oldCoreTotal S) (oldCoreYS S) (oldCoreS S) →
    upstreamCellCost (oldCoreTotal S) (oldCoreYS S) (oldCoreS S) +
        legacyFixedCost6750 S F ≤
      ContactMovingProtocol6750Research.mcaBudget

 

def DirectOldGLedger6750 : Prop :=
  ∀ (u0 u1 : I → K) (S : SelectedInterpolants6750 u0 u1),
    LegacyOldGCell S →
    ¬ OrdinaryHardCell (oldCoreTotal S) (oldCoreYS S) (oldCoreS S) →
    upstreamCellCost (oldCoreTotal S) (oldCoreYS S) (oldCoreS S) +
        factorEquationCost (oldCommonCore S) ≤
      ContactMovingProtocol6750Research.mcaBudget

 

theorem fixedSeeds_card_le_legacy_rule
    (zero : CanonicalZeroCountProvider6750)
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (F : CanonicalOldCoreFactorization S)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    (fixedSeeds selected Gamma S.QA S.QB S.QC).card ≤
      legacyFixedCost6750 S F := by
  let Delta := fixedSeeds selected Gamma S.QA S.QB S.QC
  have hzero := zero u0 u1 S F selected Gamma
    hdegree hagreement hnoPencil
  have hnonzero := commonCoreNonzeroSeeds_card_le_routed
    S F selected Gamma hdegree hagreement hnoPencil
  rw [← commonCore_branch_card_partition
    (canonicalOldCoreH S) selected Delta]
  simpa only [legacyFixedCost6750, Delta] using
    (Nat.add_le_add hzero hnonzero)

 
theorem oldCoreResidualValidity6750
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1) :
    ResidualCellValidity6750
      (oldCoreTotal S - 1) (oldCoreYS S - 1)
        (oldCoreS S - 1) (oldCoreS S) := by
  let tf : Fin 1667 := ⟨oldCoreTotal S,
    Nat.lt_succ_iff.mpr (oldCommonCore_total_le S)⟩
  let yf : Fin 66 := ⟨oldCoreYS S,
    Nat.lt_succ_iff.mpr (oldCommonCore_ys_le S)⟩
  let rf : Fin 15 := ⟨oldCoreS S,
    Nat.lt_succ_iff.mpr (oldCommonCore_slope_le S)⟩
  simpa only [tf, yf, rf] using
    residualCellValidity_of_bounded_cell tf yf rf

 


theorem legacyOldGCountProvider6750_of_receipts
    (zero : CanonicalZeroCountProvider6750)
    (hardLedger : LegacyOldGLedger6750)
    (directLedger : DirectOldGLedger6750) :
    LegacyOldGCountProvider6750 := by
  intro u0 u1 S selected Gamma hdegree hagreement hnoPencil hlegacy
  have hupstream := upstream_partition_card_le_of_source_caps
    S selected Gamma hdegree hagreement hnoPencil
      (oldCoreResidualValidity6750 S)
  have hpartition := (partition_card selected Gamma S.QA S.QB S.QC).symm
  by_cases hhard : OrdinaryHardCell
      (oldCoreTotal S) (oldCoreYS S) (oldCoreS S)
  · obtain ⟨F⟩ := exists_canonicalOldCoreFactorization S
    have hfixed := fixedSeeds_card_le_legacy_rule
      zero S F selected Gamma hdegree hagreement hnoPencil
    rw [hpartition]
    exact (Nat.add_le_add hupstream hfixed).trans
      (hardLedger u0 u1 S F hhard)
  · have hfixed := fixedSeeds_card_le_direct_oldCore
      S selected Gamma hdegree hagreement hnoPencil
    rw [hpartition]
    exact (Nat.add_le_add hupstream hfixed).trans
      (directLedger u0 u1 S hlegacy hhard)

end

end ContactLegacyOldGCountProvider6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactLegacyOldGCountProvider6750Research.commonCoreNonzeroSeeds_card_le_routed
#print axioms ProximityPrize.SubmissionLower.ContactLegacyOldGCountProvider6750Research.fixedSeeds_card_le_legacy_rule
#print axioms ProximityPrize.SubmissionLower.ContactLegacyOldGCountProvider6750Research.legacyOldGCountProvider6750_of_receipts
