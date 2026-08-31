import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactLegacyOldGCountProvider6750Research
import ProximityPrize.SubmissionLower.ContactCanonicalHighSourceStageBound6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredShellHighSource6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredOrdinaryTangent6750Research

 









namespace ProximityPrize.SubmissionLower
namespace ContactLegacyCanonicalAnchoredZero6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactTranslation
open ContactPrimeSeedIncidence
open ContactProperCutSeedCount
open ContactTwoTailParameters6750Research
open ContactStackedSeedPartition6670Research
open ContactCommonCoreBranchPartition6750Research
open ContactAnchoredOneFamilySelector6750Research
open ContactAnchoredHardCellSelector6750Research
open ContactOrdinaryHardShell6750Research
open ContactAnchoredHighSourceHull6750Research
open ContactAnchoredHighSourceAssembly6750Research
open ContactAnchoredCanonicalHighSourceEndToEnd6750Research
open ContactAnchoredOrdinaryTangent6750Research
open ContactCanonicalHighSourceAnchoredCap6750Research
open ContactCanonicalHighSourceStageBound6750Research
open ContactSelectedCount6750Research
open ContactLegacyCanonicalSource6750Research
open ContactLegacyTwoFactorEasy6750Research
open ContactLegacyOldGCountProvider6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 300000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

 

theorem canonicalAnchoredZeroCountProvider6750_closed :
    CanonicalAnchoredZeroCountProvider6750 := by
  intro u0 u1 S F selected Gamma hdegree hagreement hnoPencil cell
  let Delta := fixedSeeds selected Gamma S.QA S.QB S.QC
  let g := oldCommonCoreHighArray S
  let H := canonicalHighSourceCore IRSProfile.domain u0 u1 g
  let c := canonicalCoreContact u0 u1 g
  let t := canonicalCoreTotal u0 u1 g
  let y := canonicalCoreYS u0 u1 g
  let r := canonicalCoreS u0 u1 g
  let source : FixedHighSourceCertificate g selected Delta :=
    fixedHighSourceCertificate_of_oldCommonCore S selected Gamma
  let semantics : FixedCandidateSemantics IRSProfile.domain u0 u1
      selected Delta :=
    fixedCandidateSemantics_of_counts S selected Gamma hdegree hagreement
  have hcell : OrdinaryHardCell t y r := by
    simpa [t, y, r, g, canonicalOldCoreH, factorTotal, factorYS, factorS,
      canonicalCoreTotal, canonicalCoreYS, canonicalCoreS] using cell
  have hnoDelta : NoLargeSelectedPencil selected Delta w errors := by
    apply noLargeSelectedPencil_mono selected Gamma Delta w errors
    · exact fixedSeeds_subset selected Gamma S.QA S.QB S.QC
    · exact hnoPencil
  have hstage : CanonicalHighSourceStageBound u0 u1 g selected Delta
      (canonicalAnchoredCost t y r) := by
    simpa only [t, y, r] using
      (canonicalHighSourceStageBoundExact_of_ordinaryHard_tangents
        u0 u1 g selected Delta source semantics hcell hnoDelta
          (cellTangentProvider6750 t y r)
          (cellTangentProvider6750
            (quotientTotal t y r) (quotientYS y) (quotientS r)))
  have hcardI : Fintype.card I = domainSize := by
    norm_num [I, IRSProfile.Index, domainSize]
  have hHcontact : MvPolynomial.weightedTotalDegree
      (ContactFactorCaps.contactWeights 131071) H = c := rfl
  have hHtotal : MvPolynomial.weightedTotalDegree
      ContactIdentityResidualGlobalFlagResearch.residualTotalWeights H = t := rfl
  have hHys : MvPolynomial.weightedTotalDegree
      ContactIdentityResidualGlobalFlagResearch.residualYSWeights H = y := rfl
  have hHs : MvPolynomial.weightedTotalDegree
      ContactIdentityResidualGlobalFlagResearch.residualSWeights H = r := rfl
  by_cases hhard : HardCell t y r
  · have hcount :=
      ContactAnchoredHighSourceAssembly6750Research.HardCell.commonCoreZeroSeeds_card_le_of_highSourceHull
        hhard IRSProfile.domain u0 u1 hcardI g
          source.source_ne_zero source.source_mem_fiveCap
          hHcontact hHtotal hHys hHs selected Delta semantics
          (canonicalAnchoredCost t y r) hstage
    simpa [Delta, H, g, t, y, r, canonicalOldCoreH, factorTotal,
      factorYS, factorS, canonicalCoreTotal, canonicalCoreYS, canonicalCoreS]
      using hcount
  · have hshell : FirstDerivativeShell t y r := ⟨hcell, hhard⟩
    have hcount :=
      ContactAnchoredHighSourceAssembly6750Research.FirstDerivativeShell.commonCoreZeroSeeds_card_le_of_highSourceHull
        hshell IRSProfile.domain u0 u1 hcardI g
          source.source_ne_zero source.source_mem_fiveCap
          hHcontact hHtotal hHys hHs selected Delta semantics
          (canonicalAnchoredCost t y r) hstage
    simpa [Delta, H, g, t, y, r, canonicalOldCoreH, factorTotal,
      factorYS, factorS, canonicalCoreTotal, canonicalCoreYS, canonicalCoreS]
      using hcount

 

theorem canonicalZeroCountProvider6750_closed :
    CanonicalZeroCountProvider6750 :=
  canonicalZeroCountProvider6750_of_anchored
    canonicalAnchoredZeroCountProvider6750_closed

end
end ContactLegacyCanonicalAnchoredZero6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactLegacyCanonicalAnchoredZero6750Research.canonicalAnchoredZeroCountProvider6750_closed
#print axioms ProximityPrize.SubmissionLower.ContactLegacyCanonicalAnchoredZero6750Research.canonicalZeroCountProvider6750_closed
