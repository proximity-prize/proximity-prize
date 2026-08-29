import ProximityPrize.SubmissionLower.ContactStackedResidualCells6656Research
import ProximityPrize.SubmissionLower.ContactStackedSeedPartition6670Research
import ProximityPrize.SubmissionLower.ContactStackedBoxTransport6670Research
import ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6670Research

/-!
# Actual recursive-GCD residual cells at score 67.30

The first cell uses the profile-B quotient as singular pivot and the profile-A
quotient as external proper cut.  The second uses the A/B-GCD quotient as
pivot and the profile-C quotient as cut.  The accepted asymmetric regular and
parameterized tight-singular providers close both cells; this module supplies
only their target-specific boxes, seed equations, and arithmetic gates.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedResidualCells6670Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactInterpolation ContactTranslation ContactFactorCaps
open ContactPrimeSeedIncidence ContactProperCutSeedCount ContactRecursiveGCDResearch
open ContactStackedParameters6670Research
open ContactStackedGCDCover6670Research
open ContactStackedSeedPartition6670Research
open ContactStackedBoxTransport6670Research
open ContactTightSingularLedgerResearch
open ContactSingularLedger6600Research
open ContactSingularBranch6600Research
open ContactAsymmetricResidualStageResearch
open ContactRecursiveResidualStages6656Research

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
  ContactRecursiveResidualStages6670Research.residualStageOne
def stageTwo : UnequalParameters :=
  ContactRecursiveResidualStages6670Research.residualStageTwo
def pivotB : TightParameters := ContactRecursiveResidualStages6670Research.pivotB
def pivotGcd12 : TightParameters :=
  ContactRecursiveResidualStages6670Research.pivotGcd12

attribute [local simp] stageOne stageTwo pivotB pivotGcd12
attribute [local simp]
  ContactRecursiveResidualStages6670Research.residualStageOne
  ContactRecursiveResidualStages6670Research.residualStageTwo
  ContactRecursiveResidualStages6670Research.pivotB
  ContactRecursiveResidualStages6670Research.pivotGcd12

theorem firstResidualCell_count_lt
    (QA QB : StackedPoly) (hQA : QA ≠ 0) (hQB : QB ≠ 0)
    (hboxA : QA ∈ globalCoefficientBox IRSProfile.Field
      (50 * agreements) w 25000 15)
    (hboxB : QB ∈ globalCoefficientBox IRSProfile.Field
      (60 * agreements) w 3100 18)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (Gamma : Finset IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (hcover : ∀ gamma ∈ Gamma,
      (specialization IRSProfile.Field (selected gamma) gamma (gcd12 QA QB) ≠ 0 ∧
        specialization IRSProfile.Field (selected gamma) gamma (quotientA QA QB) = 0 ∧
        specialization IRSProfile.Field (selected gamma) gamma (quotientB QA QB) = 0) ∨
      (specialization IRSProfile.Field (selected gamma) gamma (gcd12 QA QB) = 0))
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ ((Finset.univ : Finset IRSProfile.Index).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    (firstResidualSeeds selected Gamma QA QB).card <
      96625554990674 + 639622355847463 := by
  let Delta := firstResidualSeeds selected Gamma QA QB
  let Q := quotientB QA QB
  let T := quotientA QA QB
  have hsub : Delta ⊆ Gamma := by
    simpa [Delta] using firstResidualSeeds_subset selected Gamma QA QB
  have hsolutions := firstResidualSeeds_quotient_vanish selected Gamma QA QB hcover
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
  have hTcaps := degree_bounds_of_mem_box T (50 * agreements) w 25000 15
    (by norm_num [w]) hTbox
  have hrel : IsRelPrime Q T := firstQuotients_isRelPrime hQB
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
  have hnoPencilDelta : NoLargeSelectedPencil selected Delta
      pivotB.w pivotB.errors := by
    simpa [pivotB, TightParameters.errors, errors, n, agreements, w] using
      noLargeSelectedPencil_mono selected Gamma Delta w errors hsub hnoPencil
  have hstage :=
    ContactStackedResidualCells6656Research.asymmetric_stage_count_lt_of_regular_factors
      stageOne pivotB Q T hQ prime
      (by norm_num [pivotB])
      (by norm_num [pivotB, prime])
      (by norm_num [pivotB])
      (by norm_num [pivotB, prime])
      (by norm_num [pivotB, TightParameters.kappa])
      (by norm_num [pivotB, TightParameters.algebraicCap,
        TightParameters.kappa])
      (by norm_num [pivotB, prime, TightParameters.implicitYCap,
        TightParameters.kappa])
      (by norm_num [pivotB, prime, TightParameters.algebraicCap,
        TightParameters.kappa])
      (by norm_num [pivotB, prime, TightParameters.implicitYCap,
        TightParameters.algebraicCap, TightParameters.kappa])
      (by norm_num [pivotB])
      (by norm_num [pivotB])
      hQbox
      (by norm_num [stageOne, UnequalParameters.gap])
      (by norm_num [stageOne, pivotB, UnequalParameters.gap,
        TightParameters.gap])
      (by norm_num [stageOne, pivotB])
      (by norm_num [stageOne, pivotB])
      (by norm_num [stageOne, pivotB])
      selected Delta (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain
      u0 u1 IRSProfile.domain.injective.injOn
      (by norm_num [IRSProfile.Index, pivotB])
      hdegreeDelta hQsolution hTsolution hagreementDelta hnoPencilDelta
      (all_regularPairSeeds_bound stageOne Q T hQ hrel
        pivotB.D pivotB.w pivotB.L pivotB.s prime hQbox
        (by norm_num [pivotB])
        (by norm_num [stageOne, pivotB])
        (by norm_num [stageOne, pivotB])
        (by norm_num [stageOne, pivotB])
        (by simpa [stageOne, agreements, w] using hTcaps.1)
        (by simpa [stageOne] using hTcaps.2.1)
        (by simpa [stageOne] using hTcaps.2.2)
        (by norm_num [stageOne])
        (by norm_num [stageOne, prime])
        (by norm_num [stageOne, prime])
        (by norm_num [stageOne, prime])
        (by norm_num [stageOne, UnequalParameters.mixedCost, prime])
        (by norm_num [stageOne, UnequalParameters.mixedCost, prime])
        (by norm_num [stageOne, UnequalParameters.mixedCost, prime])
        selected Delta (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain
        u0 u1 IRSProfile.domain.injective.injOn
        (by norm_num [IRSProfile.Index, stageOne])
        (by norm_num [stageOne])
        (by norm_num [stageOne, prime])
        (by norm_num [stageOne])
        (by norm_num [stageOne])
        (by simpa [stageOne, pivotB] using hdegreeDelta)
        (by simpa [stageOne, pivotB] using hagreementDelta)
        (by simpa [stageOne, pivotB, UnequalParameters.errors,
          TightParameters.errors] using hnoPencilDelta))
  have hceil : stageOne.regularCountCap + pivotB.countCap + 1 =
      96625554990674 + 639622355847463 := by
    simpa only [stageOne, pivotB,
      ContactRecursiveResidualStages6670Research.firstResidualSingularCeiling] using
      ContactRecursiveResidualStages6670Research.residual_singular_ceilings.1
  rw [hceil] at hstage
  simpa [Delta] using hstage

theorem secondResidualCell_count_lt
    (QA QB QC : StackedPoly) (hQA : QA ≠ 0) (hQB : QB ≠ 0) (hQC : QC ≠ 0)
    (hboxA : QA ∈ globalCoefficientBox IRSProfile.Field
      (50 * agreements) w 25000 15)
    (hboxB : QB ∈ globalCoefficientBox IRSProfile.Field
      (60 * agreements) w 3100 18)
    (hboxC : QC ∈ globalCoefficientBox IRSProfile.Field
      (50 * agreements) w 800000 15)
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
      1692624412238996 + 17040508075070 := by
  let Delta := secondResidualSeeds selected Gamma QA QB QC
  let Q := middleQuotient QA QB QC
  let T := quotientC QA QB QC
  have hsub : Delta ⊆ Gamma := by
    simpa [Delta] using secondResidualSeeds_subset selected Gamma QA QB QC
  have hsolutions := secondResidualSeeds_quotient_vanish selected Gamma
    QA QB QC hcover
  have hQsolution : ∀ gamma ∈ Delta,
      specialization IRSProfile.Field (selected gamma) gamma Q = 0 :=
    fun gamma hgamma => (hsolutions gamma hgamma).1
  have hTsolution : ∀ gamma ∈ Delta,
      specialization IRSProfile.Field (selected gamma) gamma T = 0 :=
    fun gamma hgamma => (hsolutions gamma hgamma).2
  have hbox12 := gcd12_mem_meet_box QA QB hQA hQB hboxA hboxB
  have hQ : Q ≠ 0 :=
    ContactStackedResidualCells6656Research.middleQuotient_ne_zero QA QB QC hQA
  have hQbox := middleQuotient_mem_parent_box QA QB QC hQA hbox12
  have hTbox := quotientC_mem_parent_box QA QB QC hQC hboxC
  have hTcaps := degree_bounds_of_mem_box T (50 * agreements) w 800000 15
    (by norm_num [w]) hTbox
  have hrel : IsRelPrime Q T := secondQuotients_isRelPrime hQA
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
  have hnoPencilDelta : NoLargeSelectedPencil selected Delta
      pivotGcd12.w pivotGcd12.errors := by
    simpa [pivotGcd12, TightParameters.errors, errors, n, agreements, w] using
      noLargeSelectedPencil_mono selected Gamma Delta w errors hsub hnoPencil
  have hstage :=
    ContactStackedResidualCells6656Research.asymmetric_stage_count_lt_of_regular_factors
      stageTwo pivotGcd12 Q T hQ prime
      (by norm_num [pivotGcd12])
      (by norm_num [pivotGcd12, prime])
      (by norm_num [pivotGcd12])
      (by norm_num [pivotGcd12, prime])
      (by norm_num [pivotGcd12, TightParameters.kappa])
      (by norm_num [pivotGcd12, TightParameters.algebraicCap,
        TightParameters.kappa])
      (by norm_num [pivotGcd12, prime, TightParameters.implicitYCap,
        TightParameters.kappa])
      (by norm_num [pivotGcd12, prime, TightParameters.algebraicCap,
        TightParameters.kappa])
      (by norm_num [pivotGcd12, prime, TightParameters.implicitYCap,
        TightParameters.algebraicCap, TightParameters.kappa])
      (by norm_num [pivotGcd12])
      (by norm_num [pivotGcd12])
      hQbox
      (by norm_num [stageTwo, UnequalParameters.gap])
      (by norm_num [stageTwo, pivotGcd12, UnequalParameters.gap,
        TightParameters.gap])
      (by norm_num [stageTwo, pivotGcd12])
      (by norm_num [stageTwo, pivotGcd12])
      (by norm_num [stageTwo, pivotGcd12])
      selected Delta (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain
      u0 u1 IRSProfile.domain.injective.injOn
      (by norm_num [IRSProfile.Index, pivotGcd12])
      hdegreeDelta hQsolution hTsolution hagreementDelta hnoPencilDelta
      (all_regularPairSeeds_bound stageTwo Q T hQ hrel
        pivotGcd12.D pivotGcd12.w pivotGcd12.L pivotGcd12.s prime hQbox
        (by norm_num [pivotGcd12])
        (by norm_num [stageTwo, pivotGcd12])
        (by norm_num [stageTwo, pivotGcd12])
        (by norm_num [stageTwo, pivotGcd12])
        (by simpa [stageTwo, agreements, w] using hTcaps.1)
        (by simpa [stageTwo] using hTcaps.2.1)
        (by simpa [stageTwo] using hTcaps.2.2)
        (by norm_num [stageTwo])
        (by norm_num [stageTwo, prime])
        (by norm_num [stageTwo, prime])
        (by norm_num [stageTwo, prime])
        (by norm_num [stageTwo, UnequalParameters.mixedCost, prime])
        (by norm_num [stageTwo, UnequalParameters.mixedCost, prime])
        (by norm_num [stageTwo, UnequalParameters.mixedCost, prime])
        selected Delta (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain
        u0 u1 IRSProfile.domain.injective.injOn
        (by norm_num [IRSProfile.Index, stageTwo])
        (by norm_num [stageTwo])
        (by norm_num [stageTwo, prime])
        (by norm_num [stageTwo])
        (by norm_num [stageTwo])
        (by simpa [stageTwo, pivotGcd12] using hdegreeDelta)
        (by simpa [stageTwo, pivotGcd12] using hagreementDelta)
        (by simpa [stageTwo, pivotGcd12, UnequalParameters.errors,
          TightParameters.errors] using hnoPencilDelta))
  have hceil : stageTwo.regularCountCap + pivotGcd12.countCap + 1 =
      1692624412238996 + 17040508075070 := by
    simpa only [stageTwo, pivotGcd12,
      ContactRecursiveResidualStages6670Research.secondResidualSingularCeiling] using
      ContactRecursiveResidualStages6670Research.residual_singular_ceilings.2
  rw [hceil] at hstage
  simpa [Delta] using hstage

end

end ProximityPrize.SubmissionLower.ContactStackedResidualCells6670Research
