import ProximityPrize.SubmissionLower.ContactTwoTailFirstResidualCell6733Research
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
attribute [local simp] n errors agreements stageOne stageTwo pivotB pivotGcd12
attribute [local simp]
  ContactTwoTailStackedResidualParameters6733Research.residualStageOne
  ContactTwoTailStackedResidualParameters6733Research.residualStageTwo
  ContactTwoTailStackedResidualParameters6733Research.pivotB
  ContactTwoTailStackedResidualParameters6733Research.pivotGcd12
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
local instance:GCDMonoid StackedPoly:=
  UniqueFactorizationMonoid.toGCDMonoid StackedPoly
local instance:CharP IRSProfile.Field prime:=by
  simpa [prime,ContactParameters6600Research.prime] using
    ContactFrozenAlignment6600Research.challenge_field_characteristic6600
theorem secondResidualCell_count_lt
    (QA QB QC:StackedPoly) (hQA:QA≠0) (hQB:QB≠0) (hQC:QC≠0)
    (hboxA:QA∈globalCoefficientBox IRSProfile.Field
      profileA.weightedCap w profileA.totalCap profileA.slopeCap)
    (hboxB:QB∈globalCoefficientBox IRSProfile.Field
      profileB.weightedCap w profileB.totalCap profileB.slopeCap)
    (hboxC:QC∈globalCoefficientBox IRSProfile.Field
      profileC.weightedCap w profileC.totalCap profileC.slopeCap)
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
    (secondResidualSeeds selected Gamma QA QB QC).card <
      1127729807323574+75606965639647:=by
  let Delta:=secondResidualSeeds selected Gamma QA QB QC
  let Q:=middleQuotient QA QB QC
  let T:=quotientC QA QB QC
  have hsub:Delta ⊆ Gamma:=by
    simpa [Delta] using secondResidualSeeds_subset selected Gamma QA QB QC
  have hsolutions:=secondResidualSeeds_quotient_vanish selected Gamma
    QA QB QC hcover
  have hQsolution:∀ gamma∈Delta,
      specialization IRSProfile.Field (selected gamma) gamma Q=0:=
    fun gamma hgamma↦(hsolutions gamma hgamma).1
  have hTsolution:∀ gamma∈Delta,
      specialization IRSProfile.Field (selected gamma) gamma T=0:=
    fun gamma hgamma↦(hsolutions gamma hgamma).2
  have hbox12:=gcd12_mem_meet_box QA QB hQA hQB hboxA hboxB
  have hQ:Q≠0:=
    ContactStackedResidualCells6656Research.middleQuotient_ne_zero QA QB QC hQA
  have hQbox:=middleQuotient_mem_parent_box QA QB QC hQA hbox12
  have hTbox:=quotientC_mem_parent_box QA QB QC hQC hboxC
  have hTcaps:=degree_bounds_of_mem_box T profileC.weightedCap w
    profileC.totalCap profileC.slopeCap (by norm_num [w,profileC]) hTbox
  have hrel:IsRelPrime Q T:=secondQuotients_isRelPrime hQA
  have hdegreeDelta:∀ gamma∈Delta,
      (selected gamma).natDegree ≤ pivotGcd12.w:=by
    intro gamma hgamma
    simpa [pivotGcd12,w] using hdegree gamma (hsub hgamma)
  have hagreementDelta:∀ gamma∈Delta,
      pivotGcd12.a ≤ ((Finset.univ:Finset IRSProfile.Index).filter (fun i↦
        (selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i)).card:=by
    intro gamma hgamma
    simpa [pivotGcd12,agreements] using hagreement gamma (hsub hgamma)
  have hnoPencilDelta:NoLargeSelectedPencil selected Delta
      pivotGcd12.w pivotGcd12.errors:=by
    simpa [pivotGcd12,TightParameters.errors,errors,n,agreements,w] using
      noLargeSelectedPencil_mono selected Gamma Delta w errors hsub hnoPencil
  have hstage:=
    ContactStackedResidualCells6656Research.asymmetric_stage_count_lt_of_regular_factors
      stageTwo pivotGcd12 Q T hQ prime
      (by norm_num [pivotGcd12])
      (by norm_num [pivotGcd12,prime])
      (by norm_num [pivotGcd12])
      (by norm_num [pivotGcd12,prime])
      (by norm_num [pivotGcd12,TightParameters.kappa])
      (by norm_num [pivotGcd12,TightParameters.algebraicCap,TightParameters.kappa])
      (by norm_num [pivotGcd12,prime,TightParameters.implicitYCap,TightParameters.kappa])
      (by norm_num [pivotGcd12,prime,TightParameters.algebraicCap,TightParameters.kappa])
      (by norm_num [pivotGcd12,prime,TightParameters.implicitYCap,
        TightParameters.algebraicCap,TightParameters.kappa])
      (by norm_num [pivotGcd12])
      (by norm_num [pivotGcd12])
      hQbox
      (by norm_num [stageTwo,UnequalParameters.gap])
      (by norm_num [stageTwo,pivotGcd12,UnequalParameters.gap,TightParameters.gap])
      (by norm_num [stageTwo,pivotGcd12])
      (by norm_num [stageTwo,pivotGcd12])
      (by norm_num [stageTwo,pivotGcd12])
      selected Delta (Finset.univ:Finset IRSProfile.Index) IRSProfile.domain
      u0 u1 IRSProfile.domain.injective.injOn
      (by norm_num [IRSProfile.Index,pivotGcd12])
      hdegreeDelta hQsolution hTsolution hagreementDelta hnoPencilDelta
      (all_regularPairSeeds_bound stageTwo Q T hQ hrel
        pivotGcd12.D pivotGcd12.w pivotGcd12.L pivotGcd12.s prime hQbox
        (by norm_num [pivotGcd12])
        (by norm_num [stageTwo,pivotGcd12])
        (by norm_num [stageTwo,pivotGcd12])
        (by norm_num [stageTwo,pivotGcd12])
        (by
          norm_num [stageTwo,profileC,Profile.weightedCap,agreements,w] at hTcaps ⊢
          exact hTcaps.1)
        (by simpa [stageTwo,profileC] using hTcaps.2.1)
        (by simpa [stageTwo,profileC] using hTcaps.2.2)
        (by norm_num [stageTwo])
        (by norm_num [stageTwo,prime])
        (by norm_num [stageTwo,prime])
        (by norm_num [stageTwo,prime])
        (by norm_num [stageTwo,UnequalParameters.mixedCost,prime])
        (by norm_num [stageTwo,UnequalParameters.mixedCost,prime])
        (by norm_num [stageTwo,UnequalParameters.mixedCost,prime])
        selected Delta (Finset.univ:Finset IRSProfile.Index) IRSProfile.domain
        u0 u1 IRSProfile.domain.injective.injOn
        (by norm_num [IRSProfile.Index,stageTwo])
        (by norm_num [stageTwo])
        (by norm_num [stageTwo,prime])
        (by norm_num [stageTwo])
        (by norm_num [stageTwo])
        (by simpa [stageTwo,pivotGcd12] using hdegreeDelta)
        (by simpa [stageTwo,pivotGcd12] using hagreementDelta)
        (by simpa [stageTwo,pivotGcd12,UnequalParameters.errors,
          TightParameters.errors] using hnoPencilDelta))
  have hceil:stageTwo.regularCountCap+pivotGcd12.countCap+1=
      1127729807323574+75606965639647:=by
    simpa only [stageTwo,pivotGcd12,
      ContactTwoTailParameters6733Research.secondResidualRegularCost,
      ContactTwoTailParameters6733Research.secondResidualSingularCost] using
      ContactTwoTailStackedResidualParameters6733Research.residual_stage_ceilings.2
  rw [hceil] at hstage
  simpa [Delta] using hstage
end
end ProximityPrize.SubmissionLower.ContactTwoTailResidualCells6733Research
