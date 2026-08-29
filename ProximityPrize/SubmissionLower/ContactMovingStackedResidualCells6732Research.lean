import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingParameters6732Research
import ProximityPrize.SubmissionLower.ContactMovingStackedResidualParameters6732Research
import ProximityPrize.SubmissionLower.ContactMovingStackedBoxTransport6732Research
import ProximityPrize.SubmissionLower.ContactStackedGCDCover6670Research
import ProximityPrize.SubmissionLower.ContactStackedResidualCells6656Research
import ProximityPrize.SubmissionLower.ContactFrozenAlignment6600Research

namespace ProximityPrize.SubmissionLower.ContactMovingStackedResidualCells6732Research

open ProximityPrize.Benchmark
open ContactStackedGCDCover6670Research
open ContactStackedResidualCells6656Research
open ContactMovingParameters6732Research
open ContactMovingStackedResidualParameters6732Research
open ContactMovingStackedBoxTransport6732Research

noncomputable section

set_option maxHeartbeats 6000000
set_option maxRecDepth 35000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

abbrev StackedPoly := MvPolynomial (Fin 4) IRSProfile.Field

local instance : GCDMonoid StackedPoly :=
  UniqueFactorizationMonoid.toGCDMonoid StackedPoly

local instance : CharP IRSProfile.Field prime := by
  simpa [prime, ContactParameters6600Research.prime] using
    ContactFrozenAlignment6600Research.challenge_field_characteristic6600

def stageOne : UnequalParameters :=
  ContactMovingStackedResidualParameters6732Research.residualStageOne

def stageTwo : UnequalParameters :=
  ContactMovingStackedResidualParameters6732Research.residualStageTwo

def pivotB : TightParameters := ContactMovingStackedResidualParameters6732Research.pivotB
def pivotGcd12 : TightParameters :=
  ContactMovingStackedResidualParameters6732Research.pivotGcd12

attribute [local simp] stageOne stageTwo pivotB pivotGcd12
attribute [local simp]
  ContactMovingStackedResidualParameters6732Research.residualStageOne
  ContactMovingStackedResidualParameters6732Research.residualStageTwo
  ContactMovingStackedResidualParameters6732Research.pivotB
  ContactMovingStackedResidualParameters6732Research.pivotGcd12

theorem firstResidualCell_count_lt
    (QA QB QC : StackedPoly) (hQA : QA ≠ 0) (hQB : QB ≠ 0)
    (hboxA : QA ∈ globalCoefficientBox IRSProfile.Field
      (47 * agreements) w 10000 12)
    (hboxB : QB ∈ globalCoefficientBox IRSProfile.Field
      (76 * agreements) w 1340 22)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (Gamma : Finset IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (hcover : ∀ gamma ∈ Gamma,
      RecursiveSpecializationBranch (selected gamma) gamma QA QB QC)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ ((Finset.univ : Finset IRSProfile.Index).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    (firstResidualSeeds selected Gamma QA QB).card <
      51333878295457 + 528903764285147 := by
  let Delta := firstResidualSeeds selected Gamma QA QB
  let Q := quotientB QA QB
  let T := quotientA QA QB
  have hsub : Delta ⊆ Gamma := by
    simpa [Delta] using firstResidualSeeds_subset selected Gamma QA QB
  have hsolutions := firstResidualSeeds_quotient_vanish selected Gamma
    QA QB QC hcover
  have hQsolution : ∀ gamma ∈ Delta,
      specialization IRSProfile.Field (selected gamma) gamma Q = 0 :=
    fun gamma hgamma => (hsolutions gamma hgamma).2
  have hTsolution : ∀ gamma ∈ Delta,
      specialization IRSProfile.Field (selected gamma) gamma T = 0 :=
    fun gamma hgamma => (hsolutions gamma hgamma).1
  have hQ : Q ≠ 0 :=
    ContactStackedResidualCells6656Research.quotientB_ne_zero QA QB hQB
  have hQbox := quotientB_mem_parent_box QA QB hQB hboxB
  have hTbox := quotientA_mem_parent_box QA QB hQA hboxA
  have hTcaps := degree_bounds_of_mem_box T (47 * agreements) w 10000 12
    (by norm_num [w]) hTbox
  have hrel : IsRelPrime Q T :=
    (firstQuotients_isRelPrime hQA).symm
  have hdegreeDelta : ∀ gamma ∈ Delta,
      (selected gamma).natDegree ≤ pivotB.w := by
    intro gamma hgamma
    simpa [pivotB, w] using hdegree gamma (hsub hgamma)
  have hagreementDelta : ∀ gamma ∈ Delta,
      pivotB.a ≤
        ((Finset.univ : Finset IRSProfile.Index).filter (fun i =>
          (selected gamma).eval (IRSProfile.domain i) =
            u0 i + gamma * u1 i)).card := by
    intro gamma hgamma
    simpa [pivotB, agreements] using hagreement gamma (hsub hgamma)
  have hnoPencilDelta : NoLargeSelectedPencil selected Delta pivotB.w errors :=
    noLargeSelectedPencil_mono selected Gamma Delta w errors hsub hnoPencil
  have htight :=
    residual_stage_one_count_lt stageOne pivotB Q T hQ hrel
      (by simpa [stageOne, pivotB] using hQbox)
      hTcaps.1 hTcaps.2.1 hTcaps.2.2
      (by decide) (by decide)
      selected Delta (Finset.univ : Finset IRSProfile.Index)
      IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by norm_num [IRSProfile.Index, stageOne])
      hQsolution hTsolution hdegreeDelta hagreementDelta hnoPencilDelta
  have hceil := residual_stage_ceilings.1
  have hident := ledger_identifications.1
  have hsing := ledger_identifications.2.1
  rw [hident, hsing] at hceil
  exact htight.trans_le (le_of_eq hceil)

theorem secondResidualCell_count_lt
    (QA QB QC : StackedPoly) (hQA : QA ≠ 0) (hQB : QB ≠ 0) (hQC : QC ≠ 0)
    (hboxA : QA ∈ globalCoefficientBox IRSProfile.Field
      (47 * agreements) w 10000 12)
    (hboxB : QB ∈ globalCoefficientBox IRSProfile.Field
      (76 * agreements) w 1340 22)
    (hboxC : QC ∈ globalCoefficientBox IRSProfile.Field
      (47 * agreements) w 10000 12)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (Gamma : Finset IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (hcover : ∀ gamma ∈ Gamma,
      RecursiveSpecializationBranch (selected gamma) gamma QA QB QC)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ ((Finset.univ : Finset IRSProfile.Index).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    (secondResidualSeeds selected Gamma QA QB QC).card <
      22197220217063 + 93574144160467 := by
  let Delta := secondResidualSeeds selected Gamma QA QB QC
  let Q := quotientC QA QB QC
  let T := middleQuotient QA QB QC
  have hsub : Delta ⊆ Gamma := by
    simpa [Delta] using secondResidualSeeds_subset selected Gamma QA QB QC
  have hsolutions := secondResidualSeeds_quotient_vanish selected Gamma
    QA QB QC hcover
  have hQsolution : ∀ gamma ∈ Delta,
      specialization IRSProfile.Field (selected gamma) gamma Q = 0 :=
    fun gamma hgamma => (hsolutions gamma hgamma).2
  have hTsolution : ∀ gamma ∈ Delta,
      specialization IRSProfile.Field (selected gamma) gamma T = 0 :=
    fun gamma hgamma => (hsolutions gamma hgamma).1
  have hQ : Q ≠ 0 :=
    ContactStackedResidualCells6656Research.quotientC_ne_zero QA QB QC hQC
  have hQbox := quotientC_mem_parent_box QA QB QC hQC hboxC
  have hbox12 := ContactMovingStackedBoxTransport6732Research.gcd12_mem_meet_box
    QA QB hQA hQB hboxA hboxB
  have hTbox := middleQuotient_mem_parent_box QA QB QC hQA hbox12
  have hTcaps := degree_bounds_of_mem_box T (47 * agreements) w 1340 12
    (by norm_num [w]) hTbox
  have hrel : IsRelPrime Q T :=
    (secondQuotients_isRelPrime (QA := QA) (B := QB) hQA).symm
  have hdegreeDelta : ∀ gamma ∈ Delta,
      (selected gamma).natDegree ≤ pivotGcd12.w := by
    intro gamma hgamma
    simpa [pivotGcd12, w] using hdegree gamma (hsub hgamma)
  have hagreementDelta : ∀ gamma ∈ Delta,
      pivotGcd12.a ≤
        ((Finset.univ : Finset IRSProfile.Index).filter (fun i =>
          (selected gamma).eval (IRSProfile.domain i) =
            u0 i + gamma * u1 i)).card := by
    intro gamma hgamma
    simpa [pivotGcd12, agreements] using hagreement gamma (hsub hgamma)
  have hnoPencilDelta : NoLargeSelectedPencil selected Delta pivotGcd12.w errors :=
    noLargeSelectedPencil_mono selected Gamma Delta w errors hsub hnoPencil
  have htight :=
    residual_stage_two_count_lt stageTwo pivotGcd12 Q T hQ hrel
      (by simpa [stageTwo, pivotGcd12] using hQbox)
      hTcaps.1 hTcaps.2.1 hTcaps.2.2
      (by decide) (by decide)
      selected Delta (Finset.univ : Finset IRSProfile.Index)
      IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by norm_num [IRSProfile.Index, stageTwo])
      hQsolution hTsolution hdegreeDelta hagreementDelta hnoPencilDelta
  have hceil := residual_stage_ceilings.2
  have hident := ledger_identifications.2.2.1
  have hsing := ledger_identifications.2.2.2
  rw [hident, hsing] at hceil
  exact htight.trans_le (le_of_eq hceil)

end ProximityPrize.SubmissionLower.ContactMovingStackedResidualCells6732Research
