import ProximityPrize.SubmissionLower.ContactStackedResidualCells6656Research
import ProximityPrize.SubmissionLower.ContactStackedSeedPartition6670Research
import ProximityPrize.SubmissionLower.ContactTwoTailStackedBoxTransport6733Research
import ProximityPrize.SubmissionLower.ContactTwoTailStackedResidualParameters6733Research
namespace ProximityPrize.SubmissionLower.ContactTwoTailResidualCells6733Research
open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactInterpolation ContactTranslation ContactFactorCaps
open ContactPrimeSeedIncidence ContactProperCutSeedCount ContactRecursiveGCDResearch
open ContactTwoTailParameters6733Research
open ContactStackedGCDCover6670Research ContactStackedSeedPartition6670Research
open ContactTwoTailStackedBoxTransport6733Research
open ContactTightSingularLedgerResearch ContactSingularLedger6600Research
open ContactSingularBranch6600Research ContactAsymmetricResidualStageResearch
open ContactRecursiveResidualStages6656Research
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 35000
attribute [local simp] n errors agreements
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
abbrev StackedPoly:=MvPolynomial (Fin 4) IRSProfile.Field
local instance:GCDMonoid StackedPoly:=
  UniqueFactorizationMonoid.toGCDMonoid StackedPoly
local instance:CharP IRSProfile.Field prime:=by
  simpa [prime,ContactParameters6600Research.prime] using
    ContactFrozenAlignment6600Research.challenge_field_characteristic6600
def stageOne:UnequalParameters:=
  ContactTwoTailStackedResidualParameters6733Research.residualStageOne
def stageTwo:UnequalParameters:=
  ContactTwoTailStackedResidualParameters6733Research.residualStageTwo
def pivotB:TightParameters:=
  ContactTwoTailStackedResidualParameters6733Research.pivotB
def pivotGcd12:TightParameters:=
  ContactTwoTailStackedResidualParameters6733Research.pivotGcd12
attribute [local simp] stageOne stageTwo pivotB pivotGcd12
attribute [local simp]
  ContactTwoTailStackedResidualParameters6733Research.residualStageOne
  ContactTwoTailStackedResidualParameters6733Research.residualStageTwo
  ContactTwoTailStackedResidualParameters6733Research.pivotB
  ContactTwoTailStackedResidualParameters6733Research.pivotGcd12
theorem firstResidualCell_count_lt
    (QA QB QC:StackedPoly) (hQA:QA≠0) (hQB:QB≠0)
    (hboxA:QA∈globalCoefficientBox IRSProfile.Field
      profileA.weightedCap w profileA.totalCap profileA.slopeCap)
    (hboxB:QB∈globalCoefficientBox IRSProfile.Field
      profileB.weightedCap w profileB.totalCap profileB.slopeCap)
    (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
    (Gamma:Finset IRSProfile.Field)
    (u0 u1:IRSProfile.Index → IRSProfile.Field)
    (hcover:∀ gamma∈Gamma,
      RecursiveSpecializationBranch (selected gamma) gamma QA QB QC)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
    (hagreement:∀ gamma∈Gamma,
      agreements ≤ ((Finset.univ:Finset IRSProfile.Index).filter (fun i↦
        (selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i)).card)
    (hnoPencil:NoLargeSelectedPencil selected Gamma w errors):
    (firstResidualSeeds selected Gamma QA QB).card <
      112248424128199+678257591819300:=by
  let Delta:=firstResidualSeeds selected Gamma QA QB
  let Q:=quotientB QA QB
  let T:=quotientA QA QB
  have hsub:Delta ⊆ Gamma:=by
    simpa [Delta] using firstResidualSeeds_subset selected Gamma QA QB
  have hsolutions:=firstResidualSeeds_quotient_vanish selected Gamma
    QA QB QC hcover
  have hQsolution:∀ gamma∈Delta,
      specialization IRSProfile.Field (selected gamma) gamma Q=0:=
    fun gamma hgamma↦(hsolutions gamma hgamma).2
  have hTsolution:∀ gamma∈Delta,
      specialization IRSProfile.Field (selected gamma) gamma T=0:=
    fun gamma hgamma↦(hsolutions gamma hgamma).1
  have hQ:Q≠0:=
    ContactStackedResidualCells6656Research.quotientB_ne_zero QA QB hQB
  have hQbox:=quotientB_mem_parent_box QA QB hQB hboxB
  have hTbox:=quotientA_mem_parent_box QA QB hQA hboxA
  have hTcaps:=degree_bounds_of_mem_box T profileA.weightedCap w
    profileA.totalCap profileA.slopeCap (by norm_num [w,profileA]) hTbox
  have hrel:IsRelPrime Q T:=(firstQuotients_isRelPrime hQA).symm
  have hdegreeDelta:∀ gamma∈Delta,
      (selected gamma).natDegree ≤ pivotB.w:=by
    intro gamma hgamma
    simpa [pivotB,w] using hdegree gamma (hsub hgamma)
  have hagreementDelta:∀ gamma∈Delta,
      pivotB.a ≤ ((Finset.univ:Finset IRSProfile.Index).filter (fun i↦
        (selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i)).card:=by
    intro gamma hgamma
    simpa [pivotB,agreements] using hagreement gamma (hsub hgamma)
  have hnoPencilDelta:NoLargeSelectedPencil selected Delta
      pivotB.w pivotB.errors:=by
    simpa [pivotB,TightParameters.errors,errors,n,agreements,w] using
      noLargeSelectedPencil_mono selected Gamma Delta w errors hsub hnoPencil
  have hstage:=
    ContactStackedResidualCells6656Research.asymmetric_stage_count_lt_of_regular_factors
      stageOne pivotB Q T hQ prime
      (by norm_num [pivotB])
      (by norm_num [pivotB,prime])
      (by norm_num [pivotB])
      (by norm_num [pivotB,prime])
      (by norm_num [pivotB,TightParameters.kappa])
      (by norm_num [pivotB,TightParameters.algebraicCap,TightParameters.kappa])
      (by norm_num [pivotB,prime,TightParameters.implicitYCap,TightParameters.kappa])
      (by norm_num [pivotB,prime,TightParameters.algebraicCap,TightParameters.kappa])
      (by norm_num [pivotB,prime,TightParameters.implicitYCap,
        TightParameters.algebraicCap,TightParameters.kappa])
      (by norm_num [pivotB])
      (by norm_num [pivotB])
      hQbox
      (by norm_num [stageOne,UnequalParameters.gap])
      (by norm_num [stageOne,pivotB,UnequalParameters.gap,TightParameters.gap])
      (by norm_num [stageOne,pivotB])
      (by norm_num [stageOne,pivotB])
      (by norm_num [stageOne,pivotB])
      selected Delta (Finset.univ:Finset IRSProfile.Index) IRSProfile.domain
      u0 u1 IRSProfile.domain.injective.injOn
      (by norm_num [IRSProfile.Index,pivotB])
      hdegreeDelta hQsolution hTsolution hagreementDelta hnoPencilDelta
      (all_regularPairSeeds_bound stageOne Q T hQ hrel
        pivotB.D pivotB.w pivotB.L pivotB.s prime hQbox
        (by norm_num [pivotB])
        (by norm_num [stageOne,pivotB])
        (by norm_num [stageOne,pivotB])
        (by norm_num [stageOne,pivotB])
        (by
          norm_num [stageOne,profileA,Profile.weightedCap,agreements,w] at hTcaps ⊢
          exact hTcaps.1)
        (by simpa [stageOne,profileA] using hTcaps.2.1)
        (by simpa [stageOne,profileA] using hTcaps.2.2)
        (by norm_num [stageOne])
        (by norm_num [stageOne,prime])
        (by norm_num [stageOne,prime])
        (by norm_num [stageOne,prime])
        (by norm_num [stageOne,UnequalParameters.mixedCost,prime])
        (by norm_num [stageOne,UnequalParameters.mixedCost,prime])
        (by norm_num [stageOne,UnequalParameters.mixedCost,prime])
        selected Delta (Finset.univ:Finset IRSProfile.Index) IRSProfile.domain
        u0 u1 IRSProfile.domain.injective.injOn
        (by norm_num [IRSProfile.Index,stageOne])
        (by norm_num [stageOne])
        (by norm_num [stageOne,prime])
        (by norm_num [stageOne])
        (by norm_num [stageOne])
        (by simpa [stageOne,pivotB] using hdegreeDelta)
        (by simpa [stageOne,pivotB] using hagreementDelta)
        (by simpa [stageOne,pivotB,UnequalParameters.errors,
          TightParameters.errors] using hnoPencilDelta))
  have hceil:stageOne.regularCountCap+pivotB.countCap+1=
      112248424128199+678257591819300:=by
    simpa only [stageOne,pivotB,
      ContactTwoTailParameters6733Research.firstResidualRegularCost,
      ContactTwoTailParameters6733Research.firstResidualSingularCost] using
      ContactTwoTailStackedResidualParameters6733Research.residual_stage_ceilings.1
  rw [hceil] at hstage
  simpa [Delta] using hstage
end
end ProximityPrize.SubmissionLower.ContactTwoTailResidualCells6733Research
