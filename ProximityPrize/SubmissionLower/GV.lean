import ProximityPrize.SubmissionLower.FC

set_option autoImplicit true

section
namespace ProximityPrize.SubmissionLower.ContactTwoTailIdentityStage6735Research
open ContactProperDelayedTailCertificate6735Research
open ContactGenericInitialPoint ContactGenericSurface ContactInterpolation
open ContactTaylorNumerators
open ContactIdentityCurveProvider6731Research
open ContactFirstTailIdentityIncidence6731Research
open ContactFirstTailCertificate6731Research
open ContactFlagBezout6543Research
open ContactMovingOuterBudget6719Research
open ContactTwoTailParameters6735Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 40000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {flag:FlagDegree}
variable [CharP (GenericField K) prime]
theorem identity_degree_direct_two_tail
    (flag:FlagDegree):
    (n-w)*(errors+1)*
        identityCurveDegree flag 1335 46 10 w ≤
      gap*hybridStageCost flag:=by
  norm_num [identityCurveDegree,n,w,errors,agreements,gap,
    hybridStageCost,exactFirstTailFlag,hybridCoordinateFlag,
    movingFiberFlag,movingCutFlag,tailFlag,fixedFlag,
    finalMeet,direction,paddedCut,
    ContactMovingPositiveLedger6719Research.centreFlag,
    ContactMovingPositiveLedger6719Research.directionFlag,
    flagMixed,unitZFlag,unitYZFlag,
    add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
  omega
theorem identity_degree_exact (flag:FlagDegree):
    identityCurveDegree flag 1335 46 10 w=
      3014679*flag.zOnly+6029358*flag.yz+
        380373848*flag.all:=by
  norm_num [identityCurveDegree,w,paddedCut,
    ContactMovingPositiveLedger6719Research.centreFlag,
    ContactMovingPositiveLedger6719Research.directionFlag,
    flagMixed,unitZFlag,unitYZFlag,
    add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
  ring
theorem identity_stage_card_le
    (S:Stage K I Gamma x prime flag)
    (hTail:S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hnodes:S.nodes.card=agreements+errors)
    (hagreement:∀ gamma∈Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (hbox:S.F∈globalCoefficientBox K (43*agreements) w 1394 12)
    (hflag:flag.all ≤ 12∧flag.yz+flag.all ≤ 59∧
      flag.zOnly+flag.yz+flag.all ≤ 1394):
    Gamma.card ≤ hybridStageCost flag:=by
  have hTailNumerator:S.G∣surfaceMap (polynomialEmbedding K)
      (numerator K S.F (w+1)):=
    (globalTailCut_dvd_iff (polynomialEmbedding K)
      (polynomialEmbedding_injective K) S.F (w+1) S.G).mp hTail
  have hprovider:=actual_identityCurveCountProvider S agreements hnodes
    hagreement (by decide) hTailNumerator (43*agreements) 1394 12
    (by decide) (by decide) (by decide) hbox
    (by
      refine ⟨hflag.2.1.trans_lt (by decide),hflag.1.trans_lt (by decide),
        hflag.2.2.trans_lt (by decide)⟩)
    (by
      have h:=hflag
      norm_num [prime,w] at h ⊢
      omega)
  let identityDegree:=identityCurveDegree flag 1335 46 10 w
  have hpositive:1 ≤ identityDegree:=by
    rw [show identityDegree=3014679*flag.zOnly+
        6029358*flag.yz+380373848*flag.all by
      exact identity_degree_exact flag]
    have hy:0 < S.G.degreeOf 1:=S.y_dependent
    have hdeg:=ContactFactoredFlagCount6676Research.degreeOf_le_flag_total
      S.G flag S.flag_support 1
    omega
  have hinc:=identity_surface_seed_bound S agreements identityDegree hprovider
    hagreement (by decide) (by rw [hnodes];decide) hpositive
  have hbudget:=identity_degree_direct_two_tail flag
  have hscaled:Gamma.card*gap ≤
      gap*hybridStageCost flag:=by
    calc
      Gamma.card*gap=Gamma.card*(agreements-w):=rfl
      _ ≤ (S.nodes.card-w)*(errors+1)*identityDegree:=hinc
      _=(n-w)*(errors+1)*identityDegree:=by
        rw [hnodes]
        norm_num [n,agreements,errors]
      _ ≤ gap*hybridStageCost flag:=hbudget
  apply Nat.le_of_mul_le_mul_right ?_ (by decide:0 < gap)
  simpa only [Nat.mul_comm] using hscaled
end
end ProximityPrize.SubmissionLower.ContactTwoTailIdentityStage6735Research
end
section
namespace ProximityPrize.SubmissionLower.ContactTwoTailStackedInterpolation6735Research
open ProximityPrize.Benchmark
open ContactFlagInterpolation6641Research ContactFlagRankKernel6641Research
open ContactTranslation ContactFlagKernelUniversalityResearch
open ContactTwoTailParameters6735Research ContactStackedGCDCover6670Research
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
abbrev GlobalPoly:=MvPolynomial (Fin 4) IRSProfile.Field
theorem exists_universal_interpolants
    (u0 u1:IRSProfile.Index → IRSProfile.Field):
    ∃ QA QB QC:GlobalPoly,
      QA≠0∧QA∈ContactInterpolation.globalCoefficientBox IRSProfile.Field
        profileA.weightedCap w profileA.totalCap profileA.slopeCap∧
      QB≠0∧QB∈ContactInterpolation.globalCoefficientBox IRSProfile.Field
        profileB.weightedCap w profileB.totalCap profileB.slopeCap∧
      QC≠0∧QC∈ContactInterpolation.globalCoefficientBox IRSProfile.Field
        profileC.weightedCap w profileC.totalCap profileC.slopeCap∧
      QB∈globalCoefficientBox IRSProfile.Field
        profileB.weightedCap w profileB.totalCap profileB.slopeCap∧
      ∀ gamma P (support:Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i∈support,P.eval (IRSProfile.domain i)=u0 i+gamma*u1 i) →
        specialization IRSProfile.Field P gamma QA=0∧
        specialization IRSProfile.Field P gamma QB=0∧
        specialization IRSProfile.Field P gamma QC=0:=by
  have hindex:Fintype.card IRSProfile.Index=n:=by
    norm_num [IRSProfile.Index,n]
  have hA:Fintype.card IRSProfile.Index*
      localRankBound profileA.multiplicity profileA.totalCap profileA.slopeCap <
      coefficientCount profileA.weightedCap w profileA.totalCap profileA.slopeCap:=by
    rw [hindex]
    exact interpolation_gateA_exact
  have hB:Fintype.card IRSProfile.Index*
      localRankBound profileB.multiplicity profileB.totalCap profileB.slopeCap <
      coefficientCount profileB.weightedCap w profileB.totalCap profileB.slopeCap:=by
    rw [hindex]
    exact interpolation_gateB_exact
  have hC:Fintype.card IRSProfile.Index*
      localRankBound profileC.multiplicity profileC.totalCap profileC.slopeCap <
      coefficientCount profileC.weightedCap w profileC.totalCap profileC.slopeCap:=by
    rw [hindex]
    exact interpolation_gateC_exact
  obtain ⟨thetaA,hnA,hkA⟩:=exists_nonzero_kernel_array
    IRSProfile.Field profileA.weightedCap w profileA.totalCap profileA.slopeCap
      profileA.multiplicity IRSProfile.domain u0 u1 hA
  obtain ⟨thetaB,hnB,hkB⟩:=exists_nonzero_kernel_array
    IRSProfile.Field profileB.weightedCap w profileB.totalCap profileB.slopeCap
      profileB.multiplicity IRSProfile.domain u0 u1 hB
  obtain ⟨thetaC,hnC,hkC⟩:=exists_nonzero_kernel_array
    IRSProfile.Field profileC.weightedCap w profileC.totalCap profileC.slopeCap
      profileC.multiplicity IRSProfile.domain u0 u1 hC
  have hDA:0 < profileA.weightedCap:=by decide
  have hDB:0 < profileB.weightedCap:=by decide
  have hDC:0 < profileC.weightedCap:=by decide
  have rA:=nonzero_kernel_member_universal IRSProfile.Field
    profileA.weightedCap w profileA.totalCap profileA.slopeCap profileA.multiplicity
    agreements IRSProfile.domain u0 u1 thetaA hnA (LinearMap.mem_ker.mpr hkA) hDA rfl
  have rB:=nonzero_kernel_member_universal IRSProfile.Field
    profileB.weightedCap w profileB.totalCap profileB.slopeCap profileB.multiplicity
    agreements IRSProfile.domain u0 u1 thetaB hnB (LinearMap.mem_ker.mpr hkB) hDB rfl
  have rC:=nonzero_kernel_member_universal IRSProfile.Field
    profileC.weightedCap w profileC.totalCap profileC.slopeCap profileC.multiplicity
    agreements IRSProfile.domain u0 u1 thetaC hnC (LinearMap.mem_ker.mpr hkC) hDC rfl
  let QA:=reconstruct IRSProfile.Field profileA.weightedCap w
    profileA.totalCap profileA.slopeCap thetaA
  let QB:=reconstruct IRSProfile.Field profileB.weightedCap w
    profileB.totalCap profileB.slopeCap thetaB
  let QC:=reconstruct IRSProfile.Field profileC.weightedCap w
    profileC.totalCap profileC.slopeCap thetaC
  refine ⟨QA,QB,QC,rA.1,
    flag_box_to_ordinary IRSProfile.Field _ w _ _ _ rA.2.1,
    rB.1,flag_box_to_ordinary IRSProfile.Field _ w _ _ _ rB.2.1,
    rC.1,flag_box_to_ordinary IRSProfile.Field _ w _ _ _ rC.2.1,
    rB.2.1,?_⟩
  intro gamma P support hP hcard hvalues
  exact ⟨rA.2.2 gamma P support hP hcard hvalues,
    rB.2.2 gamma P support hP hcard hvalues,
    rC.2.2 gamma P support hP hcard hvalues⟩
local instance:GCDMonoid GlobalPoly:=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
theorem exists_interpolants_with_recursive_cover
    (u0 u1:IRSProfile.Index → IRSProfile.Field):
    ∃ QA QB QC:GlobalPoly,
      QA≠0∧QA∈ContactInterpolation.globalCoefficientBox IRSProfile.Field
        profileA.weightedCap w profileA.totalCap profileA.slopeCap∧
      QB≠0∧QB∈ContactInterpolation.globalCoefficientBox IRSProfile.Field
        profileB.weightedCap w profileB.totalCap profileB.slopeCap∧
      QC≠0∧QC∈ContactInterpolation.globalCoefficientBox IRSProfile.Field
        profileC.weightedCap w profileC.totalCap profileC.slopeCap∧
      QB∈globalCoefficientBox IRSProfile.Field
        profileB.weightedCap w profileB.totalCap profileB.slopeCap∧
      ∀ gamma P (support:Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i∈support,P.eval (IRSProfile.domain i)=u0 i+gamma*u1 i) →
        RecursiveSpecializationBranch P gamma QA QB QC:=by
  obtain ⟨QA,QB,QC,hQA,hboxA,hQB,hboxB,hQC,hboxC,hflagB,hall⟩:=
    exists_universal_interpolants u0 u1
  refine ⟨QA,QB,QC,hQA,hboxA,hQB,hboxB,hQC,hboxC,hflagB,?_⟩
  intro gamma P support hP hcard hvalues
  obtain ⟨hA,hB,hC⟩:=hall gamma P support hP hcard hvalues
  exact recursive_branch_of_three_vanishings P gamma QA QB QC hA hB hC
end
end ProximityPrize.SubmissionLower.ContactTwoTailStackedInterpolation6735Research
end
section
namespace ProximityPrize.SubmissionLower.ContactTwoTailStackedResidualParameters6735Research
open ContactParameters6600Research ContactSingularLedger6600Research
open ContactRecursiveResidualStages6656Research ContactTightSingularLedgerResearch
open ContactTwoTailParameters6735Research
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def residualStageOne:UnequalParameters:=
  ⟨262144,131071,181983,116,26,1394,59,13,87761⟩
def residualStageTwo:UnequalParameters:=
  ⟨262144,131071,181983,59,13,1394,62,12,26176⟩
def pivotB:TightParameters:=
  ⟨262144,131071,181983,15286572,1394,26⟩
def pivotGcd12:TightParameters:=
  ⟨262144,131071,181983,7825269,1394,13⟩
theorem residual_stage_ceilings:
    residualStageOne.regularCountCap+pivotB.countCap+1=
      firstResidualRegularCost+firstResidualSingularCost∧
    residualStageTwo.regularCountCap+pivotGcd12.countCap+1=
      secondResidualRegularCost+secondResidualSingularCost:=by
  decide
theorem ledger_identifications:
    residualStageOne.regularCountCap=firstResidualRegularCost∧
    pivotB.countCap+1=firstResidualSingularCost∧
    residualStageTwo.regularCountCap=secondResidualRegularCost∧
    pivotGcd12.countCap+1=secondResidualSingularCost:=by
  decide
end ProximityPrize.SubmissionLower.ContactTwoTailStackedResidualParameters6735Research
end
