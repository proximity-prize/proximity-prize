import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactHighTFixedSeedRepair6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredOrdinaryTangent6750Research

 







namespace ProximityPrize.SubmissionLower
namespace ContactSmallProfileBFixedEquation6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactInterpolation ContactTranslation ContactFactorCaps
open ContactResidualSupportParametersResearch
open ContactMovingAgreementCertificate6719Research
open ContactIdentityResidualGlobalFlagResearch ContactPrimeSeedIncidence
open ContactStackedSeedPartition6670Research
open ContactTwoTailParameters6750Research
open ContactNestedFiveCapCoefficientBox6750Research
open ContactSelectedCount6750Research
open ContactSelectedOldCoreQuotientRank6750Research
open ContactSelectedOldCoreLowQuotients6750Research
open ContactHighTDerivativeRouter6750Research
open ContactHighTFixedSeedRepair6750Research
open ContactHighTFirstSurvivalRepairArithmetic6750Research
open ContactRouterCellCosts6750Research
open ContactAnchoredOrdinaryFixedCell6750Research
open ContactAnchoredOrdinaryProperProvider6750Research
open ContactAnchoredOrdinaryTangent6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 50000
set_option maxRecDepth 300000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev GlobalPoly := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

 

theorem mem_smallProfileB_globalBox_of_nested
    (Q : GlobalPoly) {D T YS S : Nat}
    (hD : D ≤ profileB.weightedCap) (hT : T ≤ 7)
    (hbox : Q ∈ nestedFiveCapCoefficientBox K D w T YS S) :
    Q ∈ globalCoefficientBox K profileB.weightedCap w 8 7 := by
  intro d hd
  have h := hbox hd
  change d 1 + d 2 + d 3 ≤ T ∧ d 1 + d 2 ≤ YS ∧
    d 2 ≤ S ∧ d 0 + w * d 1 + (w - 1) * d 2 < D at h
  exact ⟨by omega, by omega, h.2.2.2.trans_le hD⟩

 

theorem smallProfileB_support_of_nested
    (Q : GlobalPoly) {D T YS S : Nat} (hT : T ≤ 7)
    (hbox : Q ∈ nestedFiveCapCoefficientBox K D w T YS S) :
    ResidualSupportData (cellSupport 8 8 7) Q := by
  have hs : MvPolynomial.weightedTotalDegree residualSWeights Q ≤ 7 := by
    apply (weightedTotalDegree_le_iff residualSWeights Q 7).mpr
    intro d hd
    have h := hbox hd
    change d 1 + d 2 + d 3 ≤ T ∧ d 1 + d 2 ≤ YS ∧
      d 2 ≤ S ∧ d 0 + w * d 1 + (w - 1) * d 2 < D at h
    rw [weight_fin4]
    simpa [residualSWeights] using (show d 2 ≤ 7 by omega)
  have hys : MvPolynomial.weightedTotalDegree residualYSWeights Q ≤ 8 := by
    apply (weightedTotalDegree_le_iff residualYSWeights Q 8).mpr
    intro d hd
    have h := hbox hd
    change d 1 + d 2 + d 3 ≤ T ∧ d 1 + d 2 ≤ YS ∧
      d 2 ≤ S ∧ d 0 + w * d 1 + (w - 1) * d 2 < D at h
    rw [weight_fin4]
    simpa [residualYSWeights] using (show d 1 + d 2 ≤ 8 by omega)
  have htotal : MvPolynomial.weightedTotalDegree residualTotalWeights Q ≤ 8 := by
    apply (weightedTotalDegree_le_iff residualTotalWeights Q 8).mpr
    intro d hd
    have h := hbox hd
    change d 1 + d 2 + d 3 ≤ T ∧ d 1 + d 2 ≤ YS ∧
      d 2 ≤ S ∧ d 0 + w * d 1 + (w - 1) * d 2 < D at h
    rw [weight_fin4]
    simpa [residualTotalWeights] using
      (show d 1 + d 2 + d 3 ≤ 8 by omega)
  simpa only [cellSupport, cellA, cellB, cellS,
    ContactMovingAgreementCertificate6719Research.support] using
    (show ResidualSupportData ⟨7, 8, 8, by omega, by omega, by omega,
      by omega⟩ Q from ⟨hs, hys, htotal⟩)

theorem smallProfileB_identityBudget : IdentityCellBudget6750 8 8 7 := by
  apply identityCellBudget_of_basis
  constructor <;> decide

theorem smallProfileB_combinerGates :
    OrdinaryCellCombinerGatesD6750 profileB.weightedCap 8 7 := by
  constructor <;> decide

 

theorem smallProfileB_fixedEquation_count
    (Q : GlobalPoly) (hQ : Q ≠ 0)
    {D T YS S : Nat} (hD : D ≤ profileB.weightedCap) (hT : T ≤ 7)
    (hbox : Q ∈ nestedFiveCapCoefficientBox K D w T YS S)
    (selected : K → Polynomial K) (Delta : Finset K)
    (u0 u1 : I → K)
    (hsolution : ∀ gamma ∈ Delta,
      specialization K (selected gamma) gamma Q = 0)
    (hdegree : ∀ gamma ∈ Delta, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Delta, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Delta w errors) :
    Delta.card ≤ smallProfileBEquationCap := by
  have hshort : w + 1 ≤ profileB.weightedCap := by decide
  have hchar : profileB.weightedCap < prime := by decide
  have htangent : CellTangentProviderD6750 profileB.weightedCap 8 8 7 :=
    cellTangentProviderD6750 profileB.weightedCap 8 8 7 hshort hchar
  have hproper : ProperStageProviderD6750 profileB.weightedCap 8 8 7 :=
    properStageProviderD6750_of_tangent profileB.weightedCap 8 8 7
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      htangent
  have hcount := cell_count_le_ordinaryReplacementCostD
    profileB.weightedCap 8 8 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hproper smallProfileB_identityBudget
    hshort hchar smallProfileB_combinerGates Q hQ
    (mem_smallProfileB_globalBox_of_nested Q hD hT hbox)
    (smallProfileB_support_of_nested Q hT hbox)
    selected Delta u0 u1 hsolution hdegree hagreement hnoPencil
  simpa only [smallProfileBEquationCap] using hcount

set_option maxHeartbeats 800000 in
 

theorem fixedLowQuotientEquationCountProvider_of_candidate
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K) (j : Nat)
    (hhigh : 1693 ≤ oldCoreTotal S) (hj : j ≤ 14)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    FixedLowQuotientEquationCountProvider S selected
      (fixedSeeds selected Gamma S.QA S.QB S.QC) j := by
  intro z hz hQ hbox
  let Delta := fixedSeeds selected Gamma S.QA S.QB S.QC
  have hsub : Delta ⊆ Gamma := fixedSeeds_subset selected Gamma S.QA S.QB S.QC
  have hDbar : derivativeParentCutoff j -
      MvPolynomial.weightedTotalDegree (contactWeights 131071)
        (oldCommonCore S) ≤ profileB.weightedCap := by
    unfold derivativeParentCutoff
    norm_num [profileB, agreements, n, errors,
      ContactTwoTailParameters6750Research.Profile.weightedCap]
    omega
  have hT : 1700 - oldCoreTotal S ≤ 7 := by omega
  let QDelta := fixedQuotientEquationSeeds
    (oldCoreQuotientLinear S z) selected Delta
  have hsubQ : QDelta ⊆ Delta := Finset.filter_subset _ _
  have hsolution : ∀ gamma ∈ QDelta,
      specialization K (selected gamma) gamma (oldCoreQuotientLinear S z) = 0 := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2
  have hdegreeDelta : ∀ gamma ∈ QDelta,
      (selected gamma).natDegree ≤ w := by
    intro gamma hgamma
    exact hdegree gamma (hsub (hsubQ hgamma))
  have hagreementDelta : ∀ gamma ∈ QDelta, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card := by
    intro gamma hgamma
    exact hagreement gamma (hsub (hsubQ hgamma))
  have hnoPencilDelta : NoLargeSelectedPencil selected QDelta w errors :=
    ContactProperCutSeedCount.noLargeSelectedPencil_mono
      selected Gamma QDelta w errors (hsubQ.trans hsub) hnoPencil
  exact smallProfileB_fixedEquation_count (oldCoreQuotientLinear S z) hQ
    hDbar hT hbox selected QDelta u0 u1 hsolution hdegreeDelta
    hagreementDelta hnoPencilDelta

end

end ContactSmallProfileBFixedEquation6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactSmallProfileBFixedEquation6750Research.smallProfileB_fixedEquation_count
#print axioms ProximityPrize.SubmissionLower.ContactSmallProfileBFixedEquation6750Research.fixedLowQuotientEquationCountProvider_of_candidate
