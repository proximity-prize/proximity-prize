import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactLegacyCanonicalSource6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredOrdinaryTangent6750Research

 















namespace ProximityPrize.SubmissionLower
namespace ContactLegacyTwoFactorEasy6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactTranslation
open ContactFactorCaps
open ContactInterpolation
open ContactPrimeSeedIncidence
open ContactProperCutSeedCount
open ContactIdentityResidualGlobalFlagResearch
open ContactResidualSupportParametersResearch
open ContactStackedSeedPartition6670Research
open ContactTwoTailParameters6750Research
open ContactRouterCellCosts6750Research
open ContactAnchoredOrdinaryFixedCell6750Research
open ContactAnchoredOrdinaryProperProvider6750Research
open ContactAnchoredOrdinaryTangent6750Research
open ContactAnchoredHighSourceHull6750Research
open ContactAnchoredCanonicalHighSourceEndToEnd6750Research
open ContactSelectedCount6750Research
open ContactSelectedOldCoreQuotientRank6750Research
open ContactSelectedOldCoreLowQuotients6750Research
open ContactLegacyCanonicalSource6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev GlobalPoly := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

 

def factorContact (F : GlobalPoly) : Nat :=
  MvPolynomial.weightedTotalDegree (contactWeights w) F

def factorTotal (F : GlobalPoly) : Nat :=
  MvPolynomial.weightedTotalDegree residualTotalWeights F

def factorYS (F : GlobalPoly) : Nat :=
  MvPolynomial.weightedTotalDegree residualYSWeights F

def factorS (F : GlobalPoly) : Nat :=
  MvPolynomial.weightedTotalDegree residualSWeights F

 
def factorD (F : GlobalPoly) : Nat := max (w + 1) (factorContact F + 1)

def factorPaddedR (F : GlobalPoly) : Nat := max 2 (factorS F)
def factorPaddedY (F : GlobalPoly) : Nat :=
  max (factorPaddedR F + 1) (factorYS F)
def factorPaddedT (F : GlobalPoly) : Nat :=
  max (factorPaddedY F) (factorTotal F)

def factorEquationCost (F : GlobalPoly) : Nat :=
  cellRegularCost (factorPaddedT F) (factorPaddedY F) (factorPaddedR F) +
    (cellTightProfile (factorD F) (factorPaddedT F)
      (factorPaddedR F)).countCap

def factorZeroSeeds (F : GlobalPoly)
    (selected : K → Polynomial K) (Delta : Finset K) : Finset K :=
  Delta.filter (fun gamma ↦
    specialization K (selected gamma) gamma F = 0)

theorem factor_padded_basic (F : GlobalPoly) :
    2 ≤ factorPaddedR F ∧
      factorPaddedR F < factorPaddedY F ∧
      factorPaddedY F ≤ factorPaddedT F := by
  simp only [factorPaddedR, factorPaddedY, factorPaddedT]
  omega

theorem factor_coords_le_of_dvd_oldCore
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (F : GlobalPoly) (hdiv : F ∣ oldCommonCore S) :
    factorContact F ≤ 8548547 ∧ factorTotal F ≤ 1666 ∧
      factorYS F ≤ 65 ∧ factorS F ≤ 14 := by
  have hG : oldCommonCore S ≠ 0 := oldCommonCore_ne_zero S
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (weightedTotalDegree_le_of_dvd (contactWeights w)
      F (oldCommonCore S) hdiv hG).trans (oldCommonCore_contact_le S)
  · exact (weightedTotalDegree_le_of_dvd residualTotalWeights
      F (oldCommonCore S) hdiv hG).trans (oldCommonCore_total_le S)
  · exact (weightedTotalDegree_le_of_dvd residualYSWeights
      F (oldCommonCore S) hdiv hG).trans (oldCommonCore_ys_le S)
  · exact (weightedTotalDegree_le_of_dvd residualSWeights
      F (oldCommonCore S) hdiv hG).trans (oldCommonCore_slope_le S)

theorem factor_padded_caps_of_dvd_oldCore
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (F : GlobalPoly) (hdiv : F ∣ oldCommonCore S) :
    factorPaddedT F ≤ 1666 ∧ factorPaddedY F ≤ 65 ∧
      factorPaddedR F ≤ 14 := by
  have h := factor_coords_le_of_dvd_oldCore S F hdiv
  simp only [factorPaddedR, factorPaddedY, factorPaddedT]
  omega

theorem factorD_short (F : GlobalPoly) : w + 1 ≤ factorD F := by
  simp only [factorD]
  exact Nat.le_max_left _ _

theorem factorD_lt_prime_of_dvd_oldCore
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (F : GlobalPoly) (hdiv : F ∣ oldCommonCore S) :
    factorD F < prime := by
  have hc := (factor_coords_le_of_dvd_oldCore S F hdiv).1
  simp only [factorD]
  apply max_lt
  · norm_num [w, prime]
  · norm_num [prime] at ⊢
    omega

 

theorem factor_mem_exact_padded_box (F : GlobalPoly) :
    F ∈ ContactInterpolation.globalCoefficientBox K
      (factorD F) w (factorPaddedT F) (factorPaddedR F) := by
  intro d hd
  have hc := MvPolynomial.le_weightedTotalDegree (contactWeights w) hd
  have ht := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  have hr := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [contact_weight] at hc
  rw [weight_fin4] at ht hr
  simp [residualTotalWeights, residualSWeights] at ht hr
  change d 0 + w * d 1 + (w - 1) * d 2 ≤ factorContact F at hc
  change d 1 + d 2 + d 3 ≤ factorTotal F at ht
  change d 2 ≤ factorS F at hr
  change d 1 + d 3 ≤ factorPaddedT F ∧
    d 2 ≤ factorPaddedR F ∧
    d 0 + w * d 1 + (w - 1) * d 2 < factorD F
  refine ⟨?_, ?_, ?_⟩
  · apply le_trans (by omega : d 1 + d 3 ≤ d 1 + d 2 + d 3)
    exact ht.trans (Nat.le_max_right _ _)
  · exact hr.trans (Nat.le_max_right _ _)
  · exact hc.trans_lt ((Nat.lt_succ_self _).trans_le
      (Nat.le_max_right (w + 1) (factorContact F + 1)))

theorem factor_residualSupport (F : GlobalPoly) :
    ResidualSupportData
      (cellSupport (factorPaddedT F) (factorPaddedY F) (factorPaddedR F)) F := by
  have hb := factor_padded_basic F
  have hs : (cellSupport (factorPaddedT F) (factorPaddedY F)
      (factorPaddedR F)).s = factorPaddedR F := by
    simp only [cellSupport, cellS,
      ContactMovingAgreementCertificate6719Research.support]
    omega
  have hys : (cellSupport (factorPaddedT F) (factorPaddedY F)
      (factorPaddedR F)).ys = factorPaddedY F := by
    simp only [cellSupport, cellB, cellS,
      ContactMovingAgreementCertificate6719Research.support]
    omega
  have ht : (cellSupport (factorPaddedT F) (factorPaddedY F)
      (factorPaddedR F)).total = factorPaddedT F := by
    simp only [cellSupport, cellA, cellB, cellS,
      ContactMovingAgreementCertificate6719Research.support]
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]
    exact Nat.le_max_right _ _
  · rw [hys]
    exact Nat.le_max_right _ _
  · rw [ht]
    exact Nat.le_max_right _ _

 

 


structure FactorOrdinaryArithmetic (F : GlobalPoly) : Prop where
  identity : IdentityCellBudget6750
    (factorPaddedT F) (factorPaddedY F) (factorPaddedR F)
  gates : OrdinaryCellCombinerGatesD6750 (factorD F)
    (factorPaddedT F) (factorPaddedR F)

theorem factorZeroSeeds_card_le
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (F : GlobalPoly) (hF : F ≠ 0) (hdiv : F ∣ oldCommonCore S)
    (arithmetic : FactorOrdinaryArithmetic F)
    (selected : K → Polynomial K) (Gamma Delta : Finset K)
    (hDelta : Delta ⊆ Gamma)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    (factorZeroSeeds F selected Delta).card ≤ factorEquationCost F := by
  let Zs := factorZeroSeeds F selected Delta
  have hZDelta : Zs ⊆ Delta := Finset.filter_subset _ _
  have hZGamma : Zs ⊆ Gamma := hZDelta.trans hDelta
  have hcaps := factor_padded_caps_of_dvd_oldCore S F hdiv
  have hbasic := factor_padded_basic F
  have hDshort := factorD_short F
  have hDchar := factorD_lt_prime_of_dvd_oldCore S F hdiv
  have ht2530 : factorPaddedT F ≤ 2530 := hcaps.1.trans (by omega)
  have proper : ProperStageProviderD6750 (factorD F)
      (factorPaddedT F) (factorPaddedY F) (factorPaddedR F) :=
    properStageProviderD6750_of_tangent
      (factorD F) (factorPaddedT F) (factorPaddedY F) (factorPaddedR F)
      ht2530 hcaps.2.1 hcaps.2.2 hbasic.1 hbasic.2.1 hbasic.2.2
      (cellTangentProviderD6750 (factorD F)
        (factorPaddedT F) (factorPaddedY F) (factorPaddedR F)
        hDshort hDchar)
  have hsolution : ∀ gamma ∈ Zs,
      specialization K (selected gamma) gamma F = 0 := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2
  have hdegreeZ : ∀ gamma ∈ Zs, (selected gamma).natDegree ≤ w := by
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
  simpa only [Zs, factorEquationCost] using
    cell_count_le_ordinaryReplacementCostD
      (factorD F) (factorPaddedT F) (factorPaddedY F) (factorPaddedR F)
      ht2530 hcaps.2.1 hcaps.2.2 hbasic.1 hbasic.2.1 hbasic.2.2
      proper arithmetic.identity hDshort hDchar arithmetic.gates
      F hF (factor_mem_exact_padded_box F) (factor_residualSupport F)
      selected Zs u0 u1 hsolution hdegreeZ hagreementZ hnoPencilZ

 

theorem subset_factorZeroSeeds_union
    (G H Q : GlobalPoly) (selected : K → Polynomial K)
    (Delta : Finset K) (hfactor : G = H * Q)
    (hvanish : ∀ gamma ∈ Delta,
      specialization K (selected gamma) gamma G = 0) :
    Delta ⊆ factorZeroSeeds H selected Delta ∪
      factorZeroSeeds Q selected Delta := by
  intro gamma hgamma
  have hmul : specialization K (selected gamma) gamma H *
      specialization K (selected gamma) gamma Q = 0 := by
    rw [← map_mul, ← hfactor]
    exact hvanish gamma hgamma
  rcases mul_eq_zero.mp hmul with hH | hQ
  · exact Finset.mem_union.mpr <| Or.inl <|
      Finset.mem_filter.mpr ⟨hgamma, hH⟩
  · exact Finset.mem_union.mpr <| Or.inr <|
      Finset.mem_filter.mpr ⟨hgamma, hQ⟩

theorem card_le_factorZeroSeeds_add
    (G H Q : GlobalPoly) (selected : K → Polynomial K)
    (Delta : Finset K) (hfactor : G = H * Q)
    (hvanish : ∀ gamma ∈ Delta,
      specialization K (selected gamma) gamma G = 0) :
    Delta.card ≤ (factorZeroSeeds H selected Delta).card +
      (factorZeroSeeds Q selected Delta).card := by
  exact (Finset.card_le_card
    (subset_factorZeroSeeds_union G H Q selected Delta hfactor hvanish)).trans
      (Finset.card_union_le _ _)

 

def canonicalOldCoreH {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) : GlobalPoly :=
  canonicalHighSourceCore IRSProfile.domain u0 u1 (oldCommonCoreHighArray S)

structure CanonicalOldCoreFactorization
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1) where
  Q : GlobalPoly
  H_ne_zero : canonicalOldCoreH S ≠ 0
  Q_ne_zero : Q ≠ 0
  factor_eq : oldCommonCore S = canonicalOldCoreH S * Q
  contact_add : factorContact (oldCommonCore S) =
    factorContact (canonicalOldCoreH S) + factorContact Q
  total_add : oldCoreTotal S =
    factorTotal (canonicalOldCoreH S) + factorTotal Q
  ys_add : oldCoreYS S = factorYS (canonicalOldCoreH S) + factorYS Q
  slope_add : oldCoreS S = factorS (canonicalOldCoreH S) + factorS Q

theorem exists_canonicalOldCoreFactorization
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1) :
    Nonempty (CanonicalOldCoreFactorization S) := by
  have hdiv := canonicalHighSourceCore_dvd_fixed_reconstruct
    IRSProfile.domain u0 u1 (oldCommonCoreHighArray S)
  rw [reconstruct_oldCommonCoreHighArray] at hdiv
  obtain ⟨Q, hfactor⟩ := hdiv
  have hH : canonicalOldCoreH S ≠ 0 := by
    apply canonicalHighSourceCore_ne_zero_of_fixed
      IRSProfile.domain u0 u1 (oldCommonCoreHighArray S)
    rw [reconstruct_oldCommonCoreHighArray]
    exact oldCommonCore_ne_zero S
  have hQ : Q ≠ 0 := by
    intro hzero
    apply oldCommonCore_ne_zero S
    rw [hfactor, hzero, mul_zero]
  refine ⟨⟨Q, hH, hQ, hfactor, ?_, ?_, ?_, ?_⟩⟩
  · calc
      factorContact (oldCommonCore S) =
          factorContact (canonicalOldCoreH S * Q) :=
        congrArg factorContact hfactor
      _ = factorContact (canonicalOldCoreH S) + factorContact Q := by
        simpa only [factorContact] using
          weightedTotalDegree_mul (contactWeights w)
            (canonicalOldCoreH S) Q hH hQ
  · calc
      oldCoreTotal S = factorTotal (canonicalOldCoreH S * Q) := by
        change factorTotal (oldCommonCore S) = _
        exact congrArg factorTotal hfactor
      _ = factorTotal (canonicalOldCoreH S) + factorTotal Q := by
        simpa only [factorTotal] using
          weightedTotalDegree_mul residualTotalWeights
            (canonicalOldCoreH S) Q hH hQ
  · calc
      oldCoreYS S = factorYS (canonicalOldCoreH S * Q) := by
        change factorYS (oldCommonCore S) = _
        exact congrArg factorYS hfactor
      _ = factorYS (canonicalOldCoreH S) + factorYS Q := by
        simpa only [factorYS] using
          weightedTotalDegree_mul residualYSWeights
            (canonicalOldCoreH S) Q hH hQ
  · calc
      oldCoreS S = factorS (canonicalOldCoreH S * Q) := by
        change factorS (oldCommonCore S) = _
        exact congrArg factorS hfactor
      _ = factorS (canonicalOldCoreH S) + factorS Q := by
        simpa only [factorS] using
          weightedTotalDegree_mul residualSWeights
            (canonicalOldCoreH S) Q hH hQ

theorem fixedSeeds_card_le_twoFactorCost
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (F : CanonicalOldCoreFactorization S)
    (arithmeticH : FactorOrdinaryArithmetic (canonicalOldCoreH S))
    (arithmeticQ : FactorOrdinaryArithmetic F.Q)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    (fixedSeeds selected Gamma S.QA S.QB S.QC).card ≤
      factorEquationCost (canonicalOldCoreH S) + factorEquationCost F.Q := by
  let Delta := fixedSeeds selected Gamma S.QA S.QB S.QC
  have hDelta : Delta ⊆ Gamma := fixedSeeds_subset selected Gamma S.QA S.QB S.QC
  have hHdiv : canonicalOldCoreH S ∣ oldCommonCore S := ⟨F.Q, F.factor_eq⟩
  have hQdiv : F.Q ∣ oldCommonCore S := by
    refine ⟨canonicalOldCoreH S, ?_⟩
    rw [mul_comm]
    exact F.factor_eq
  have hHcount := factorZeroSeeds_card_le S (canonicalOldCoreH S)
    F.H_ne_zero hHdiv arithmeticH selected Gamma Delta hDelta
      hdegree hagreement hnoPencil
  have hQcount := factorZeroSeeds_card_le S F.Q F.Q_ne_zero hQdiv
    arithmeticQ selected Gamma Delta hDelta hdegree hagreement hnoPencil
  have hcover := card_le_factorZeroSeeds_add
    (oldCommonCore S) (canonicalOldCoreH S) F.Q selected Delta F.factor_eq
      (fixedSeeds_vanish selected Gamma S.QA S.QB S.QC)
  exact hcover.trans (Nat.add_le_add hHcount hQcount)

end

end ContactLegacyTwoFactorEasy6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactLegacyTwoFactorEasy6750Research.exists_canonicalOldCoreFactorization
#print axioms ProximityPrize.SubmissionLower.ContactLegacyTwoFactorEasy6750Research.fixedSeeds_card_le_twoFactorCost
